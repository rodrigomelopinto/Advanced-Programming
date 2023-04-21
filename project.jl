mutable struct MultiMethod1
    name::Symbol
    specializers::Array{Any}
    procedure::Function
    generic_function::Any
    slots::Array{Any}
end

mutable struct GenericFunction1
    name::Any
    methods::Array{Any}
    slots::Array{Any}
    last_method::Dict{String,Any}
    sorted_methods::Array{MultiMethod1}
end


function GenericFunction1(name,methods,slots)
    return GenericFunction1(name,methods,slots,Dict([]),[])
end

GenericFunction = GenericFunction1(:GenericFunction,[],[:name,:methods])

MultiMethod = MultiMethod1(:MultiMethod,[],(x)->nothing,GenericFunction,[:specializers,:procedure,:generic_function])

mutable struct Class1
    name::Symbol
    direct_superclasses::Array{Any}
    direct_slots::Array{Symbol}
    metaclass::Union{Class1,Missing}
    default::Union{Any,Nothing}
    getters_and_setters::Union{Dict{Symbol,Any},Nothing}
    cpl::Union{Array{Any},Nothing}
    slots::Array{Any}
end

mutable struct Instance
    class::Class1
    fields::Dict{Symbol,Any}
end

function Instance(class::Class1)
    superclasses = compute_cpl(class)
    f = Dict([])
    for cls in superclasses
        if cls.default !== nothing
            for (key, value) in getfield(cls.default,:fields)
                f[key] = value
            end
        end
    end
    return Instance(class, f)
end

function class_computations(class, default_fields, name, direct_superclasses, direct_slots)
    slots = compute_slots(class)

    # Getting the default values from the superclasses and merging them with the default values provided
    for superclass in direct_superclasses
        if getfield(superclass,:default) !== nothing
            default_fields = merge!(default_fields,copy(getfield(superclass.default,:fields))) 
        end
    end
    class.default = Instance(Class1(name, direct_superclasses, direct_slots, missing, nothing, nothing,[],
        [:name,:direct_superclasses,:direct_slots,:metaclass, :default, :getters_and_setters, :cpl]),default_fields)
    
    class.cpl = compute_cpl(class)
    gs = Dict([])
    for slot in slots
        gs[slot] = compute_getter_and_setter(class, slot, 0)
    end
    class.getters_and_setters = gs
    return class
end

function Class1(name, direct_superclasses, direct_slots, metaclass, default)
    default_fields = default
    
    class = Class1(name, direct_superclasses, direct_slots, metaclass, nothing, nothing,[],[:name,:direct_superclasses,:direct_slots, :metaclass, :default, :getters_and_setters, :cpl])

    if metaclass !== missing && metaclass.default !== nothing
        default_fields = merge!(default_fields,copy(getfield(metaclass.default,:fields)))
    end

    if name !== :Object && name !== :Top && name !== :Class && name != :BuiltInClass && name !== :_Int64 && name !== :_String && name !== :_Symbol
        class = class_computations(class, default_fields, name, direct_superclasses, direct_slots)
    end
    return class
end

generic_functions=[]
# Code to create the macro defgeneric 
macro defgeneric(name...)
    name=name[1].args[1]
    global_sym = name
    class_obj = GenericFunction1(name, [], [:name,:methods])
    push!(generic_functions,class_obj)
    quote
        global $global_sym = $class_obj
    end
end

# Code to create the macro defmethod 
macro defmethod(name)
    info=name.args[1]
    data=name.args[2]
    tmp_gen =info.args[1]
    exists=false
    #CHECKING IF THE GENERIC FUNCTION EXISTS
    for  generic in generic_functions 
        if generic.name == tmp_gen
            tmp_gen=generic
            exists=true
            break
        end
    end
    #GETTING THE GENERIC FUNCTION
    if exists == false
        global_sym = tmp_gen
        class_obj = GenericFunction1(tmp_gen, [], [:name,:methods])
        push!(generic_functions,class_obj)
        tmp_gen=class_obj
    end
    # putting the arguments into the right types
    slots_name::Vector{Symbol} = []
    slots_type=[]
    for slots in info.args[2:end]
        if string(slots)=="io"
            push!(slots_name,slots)
        elseif typeof(slots) == Symbol
            push!(slots_name,slots)
        else
            slots_data=slots.args
            push!(slots_name,slots_data[1])
            type=string(slots_data[2])
            for data_type in class1_instances
                if type == string(data_type.name)
                    push!(slots_type,data_type)
                end
            end
        end
    end
    res = Tuple(slots_name)

    # GENERATE THE EXPRESSION OF THE PROCEDURE OF THE METHOD
    expr = Expr(:function, Expr(:tuple, Symbol.(res)...), data)

    # GENERATE THE METHOD
    if exists == false
        quote
            global $global_sym = $class_obj
            push!($tmp_gen.methods,MultiMethod1($tmp_gen.name,$slots_type,
            $expr , $tmp_gen, [:specializers,:procedure,:generic_function]))
        end |> esc
    else
        quote
            push!($tmp_gen.methods,MultiMethod1($tmp_gen.name,$slots_type,
            $expr , $tmp_gen, [:specializers,:procedure,:generic_function]))
        end |> esc
    end
end

class1_instances=[]
# Code to create defclass
macro defclass(name, superclasses, slots, metaclass=missing)
    global_sym = name
    simple_slots = []
    init = Dict{Symbol,Any}([])
    readers = Dict()
    writers = Dict()
    #After getting the data now transform the slots
    if slots.args != []
        simple_slots = filter(slot -> isa(slot, Symbol), slots.args) # Slots that are symbols
        complex_slots = filter(slot -> !isa(slot, Symbol), slots.args) # Slots that are expressions
        push!(simple_slots, [isa(slot.args[1], Symbol) ? slot.args[1] : slot.args[1].args[1] for slot in complex_slots]...)
        [init[slot] = missing for slot in simple_slots]
        for slot in complex_slots
            if slot.head === :(=) # Handles cases like @defclass(A, [], [a=1, b=2])
                init[slot.args[1]] = slot.args[2]
                continue
            elseif slot.head === :vect
                field = slot.args[1] # Can be either a symbol (ex. :a) or an expression (ex. :(a=1))
                if !isa(slot.args[1], Symbol) && slot.args[1].head === :(=) # Handles cases like @defclass(A, [], [[a=1, ...], [b=2, ...]])
                    field = slot.args[1].args[1] # Becomes just a symbol (ex. a=1 --> :a)
                    init[field] = slot.args[1].args[2] 
                end
                for option in slot.args
                    if !isa(option, Symbol)
                        # Handles cases like @defclass(A, [], [[a, ..., initform=1], [b, ..., initform=2]])
                        if option.args[1] == :initform
                            init[field] = option.args[2]
                        # Handles cases like @defclass(A, [], [[a, reader=get_a, ...], [b, reader=get_b, ...]])
                        elseif option.args[1] == :reader
                            readers[field] = option.args[2]
                        # Handles cases like @defclass(A, [], [[a, writer=set_a!, ...], [b, writer=set_b!, ...]])
                        elseif option.args[1] == :writer
                            writers[field] = option.args[2]
                        end
                    end
                end
            end
        end
    end
    sym_name = Symbol(name)
    # generate the readers and writers expressions to be called on the quote block
    expr_readers = []
    for (field, reader) in readers
        aux = :(@defmethod $(Expr(:function, Expr(:call,reader,:(o::$sym_name)), Expr(:call,:getproperty,:o, QuoteNode(field)))))
        push!(expr_readers, aux)
    end

    expr_writers = []
    for (field, reader) in writers
        aux = :(@defmethod $(Expr(:function, Expr(:call,reader,:(o::$sym_name),:v), Expr(:call,:setproperty!,:o, QuoteNode(field),:v))))
        push!(expr_writers, aux)
    end
    #Generate the class itself 
    quote
        if $superclasses == []
            if $metaclass !== missing
                global $global_sym = Class1($(QuoteNode(sym_name)), [$Object], $simple_slots, $metaclass, $init)
            else
                global $global_sym = Class1($(QuoteNode(sym_name)), [$Object], $simple_slots, missing, $init)
            end
        else
            if $metaclass !== missing
                global $global_sym = Class1($(QuoteNode(sym_name)), $superclasses, $simple_slots, $metaclass, $init)
            else
                global $global_sym = Class1($(QuoteNode(sym_name)), $superclasses, $simple_slots, missing, $init)
            end
        end
        push!($class1_instances,$global_sym)
        $(expr_readers...)
        $(expr_writers...)
    end
end

Top = Class1(:Top,[],[],missing,nothing)
push!(class1_instances,Top)

Object = Class1(:Object,[Top],[],missing,nothing)
push!(class1_instances,Object)

@defclass(Class, [Object], [])
@defclass(BuiltInClass, [Top], [])
@defclass(_Int64, [Top], [], metaclass=BuiltInClass)
@defclass(_String, [Top], [], metaclass=BuiltInClass)
@defclass(_Symbol, [Top], [], metaclass=BuiltInClass)

new(class; initargs...) =
    let instance = allocate_instance(class)
        initialize(instance, initargs)
        instance
    end

function initialize(instance::Instance, initargs)
    for (key, value) in initargs
        getfield(instance,:fields)[key] = value
    end
end

function Base.getproperty(class::Class1, field::Symbol)
    if field in getfield(class,:slots) || field === :slots
        return getfield(class,field)
    else
        instance = getfield(class,:default)
        return getfield(instance,:fields)[field]
    end
end

function Base.setproperty!(class::Class1, field::Symbol, value)
    if field in getfield(class,:slots) || field === :slots
        invoke(setproperty!, Tuple{Any,Symbol,Any}, class, field, value)
    else
        instance = getfield(class,:default)
        getfield(instance,:fields)[field] = value
    end
end

function Base.getproperty(instance::Instance, field::Symbol)
    return getfield(instance,:class).getters_and_setters[field][1](instance)
end

function Base.setproperty!(instance::Instance, field::Symbol, value)
    getfield(instance,:class).getters_and_setters[field][2](instance, value)
end

function class_of(instance)
    if typeof(instance) === Int64
        return _Int64
    elseif typeof(instance) === String
        return _String
    elseif typeof(instance) === Symbol
        return _Symbol
    elseif typeof(instance) === Instance
        return getfield(instance,:class)
    elseif typeof(instance) === Class1
        if getfield(instance,:metaclass) === missing
            return Class
        else
            return getfield(instance,:metaclass)
        end
    elseif typeof(instance) === GenericFunction1
        return GenericFunction
    elseif typeof(instance) === MultiMethod1
        return MultiMethod
    end
end

function class_name(instance)
    return instance.name
end

@defgeneric print_object(obj, io)
@defmethod print_object(obj::Object, io) = print(io, "<$(class_name(class_of(obj))) $(string(objectid(obj), base=62))>")

@defmethod print_object(obj::Class, io) = print(io, "<$(class_name(class_of(obj))) $(class_name(obj))>")

@defmethod print_object(obj::Top, io) = print(io, "<$(class_name(class_of(obj))) $(class_name(obj))>")

#Since GenericFunction is not a class, we need to define a special method for it
func_print(f::GenericFunction1, io) = print(io, "<$(class_name(class_of(f))) $(class_name(f)) with $(length(f.methods)) methods>")

#Since MultiMethod is not a class, we need to define a special method for it
function func_print(m::MultiMethod1, io)
    spec = "("
    for i in m.specializers
        spec = spec * "$(class_name(i)), "
    end
    spec = spec[1:end-2] * ")"
    print(io, "<$(class_name(class_of(m))) $(class_name(m.generic_function))$(spec)>") 
end

function Base.show(io::IO, x)
    if typeof(x) === MultiMethod1 || typeof(x) === GenericFunction1
        func_print(x, io)
    else
        print_object(x, io)
    end
end

function get_applicable_methods(a::GenericFunction1, args...)
    applicable_methods = []
    size = length(args)
    if a === print_object
        size = size - 1
    end
    for method in a.methods
        k=0
        for i in 1:size
            if i > length(method.specializers)
                continue
            end
            applicable_classes = compute_cpl_normal(class_of(args[i]))
            if method.specializers[i] in applicable_classes
                k+=1
            else
                break
            end
        end
        #If all specializers are applicable, then the method is applicable
        if k == length(method.specializers)
            push!(applicable_methods, method)
        end
    end
    
    if length(applicable_methods) == 0
        no_aplicable_method(a, args)
    end
    return applicable_methods
end

gen_funs = []
function (gf::GenericFunction1)(args...)
    global gen_funs
    #Pushing the generic function to the list of generic functions for the case 
    #in which a generic_function is called inside another generic function.
    push!(gen_funs, gf)
    
    applicable_methods = get_applicable_methods(gf, args...)
    gf.sorted_methods = sortmethods(applicable_methods, args...)
    method = gf.sorted_methods[1]
    #Store the last method called and the arguments in the case call_next_method is used
    gf.last_method["method"] = 1
    gf.last_method["args"] = args
    
    result = method.procedure(args...)
    
    filter!(x -> x != gf, gen_funs)
    return result
end

function appears_last(method1::MultiMethod1, method2::MultiMethod1, cpl,j)
    for i in cpl
        if i === method1.specializers[j]
            return false
        elseif i === method2.specializers[j]
            return true
        end
    end
end
    
function sortmethods(applicable_methods,args...)
    sorted = []
    sorted = applicable_methods
    n = length(sorted)
    
    for i in 1:n
 
        for j in 1:n-i

            index = 1
            while sorted[j].specializers[index] === sorted[j+1].specializers[index]
                index += 1
            end
            if appears_last(sorted[j], sorted[j+1],compute_cpl_normal(class_of(args[index])), index)
                sorted[j], sorted[j+1] = sorted[j+1], sorted[j]
            end
        end
    end
    return sorted
end

function call_next_method()
    global gen_funs
    current_gen = gen_funs[end]

    methods = current_gen.sorted_methods
    size = length(methods)

    if current_gen.last_method["method"] == size
        return no_aplicable_method(current_gen, current_gen.last_method["args"])
    else
        current_gen.last_method["method"] += 1
        return methods[current_gen.last_method["method"]].procedure(current_gen.last_method["args"]...)
    end
end

function no_aplicable_method(gf, args)
    filter!(x -> x != gf, gen_funs)
    throw("No applicable method for $(gf.name) with arguments $(args)")
end
    

# Function to compute the class precendence list where we adopt a breadth first search
function compute_cpl_normal(cls::Class1)
    queue=[]
    result=[cls]
    queue = vcat(queue,cls.direct_superclasses)
    result = vcat(result,cls.direct_superclasses)
    while length(queue) > 0
        current = queue[1]
        queue = queue[2:end]
        for superclass in current.direct_superclasses
            if superclass ∉ result
                all_precedents_included = all(x -> x in result, superclass.direct_superclasses[2:end])
                if all_precedents_included
                    push!(result, superclass)
                    push!(queue, superclass)
                end
            end
        end
    end
    tmp_result = []
    a=[]
    for r in result
        if (r.name) == :Top  || (r.name) == :Object
            push!(a,r)
        else
            push!(tmp_result, r)
        end
    end
    tmp_result =vcat(tmp_result,a)

    return tmp_result
end

function class_direct_slots(cls::Class1)
    return getfield(cls, :direct_slots)
end

function class_slots(cls::Class1)
    superclasses = compute_cpl(cls)
    slots = []
    for superclass in superclasses
        slots = vcat(slots, class_direct_slots(superclass))
    end
    return slots
end

function class_direct_superclasses(cls::Class1)
    return getfield(cls, :direct_superclasses)
end

function class_cpl(cls::Class1)
    return compute_cpl(cls)
end

function generic_methods(gf::GenericFunction1)
    return getfield(gf, :methods)
end

function method_specializers(method::MultiMethod1)
    return getfield(method, :specializers)
end

@defgeneric allocate_instance(class)

@defmethod allocate_instance(class::Class) = Instance(class)

@defgeneric compute_slots(class)

@defmethod compute_slots(class::Class) =
vcat(map(class_direct_slots, class_cpl(class))...)

@defgeneric compute_getter_and_setter(class, slot, index)

@defmethod compute_getter_and_setter(class::Class, slot, index) = begin
    function get(instance)
        getfield(instance,:fields)[slot]
    end
    function set!(instance, value)
        getfield(instance,:fields)[slot] = value
    end
    return (get, set!)
end

@defgeneric compute_cpl(cls)

@defmethod compute_cpl(cls::Class) = compute_cpl_normal(cls)



#EXEMPLOS DO ENUNCIADO
# Exemplo 2.1
@defclass(ComplexNumber, [], [real, imag])

# Exemplo 2.2
c1 = new(ComplexNumber, real=1, imag=2)
c1.real
# Exemplo 2.3
getproperty(c1, :real)
c1.real
setproperty!(c1, :imag, -1)
c1.imag += 3

# Exemplo 2.4
@defgeneric add(a,b)

@defmethod add(a::ComplexNumber, b::ComplexNumber) = new(ComplexNumber, real=(a.real + b.real), imag=(a.imag + b.imag))
add.methods

c2 = add(c1,c1)
c1.real
c1.imag
c2.real
c2.imag

# Exemplo 2.5
@defmethod print_object(c::ComplexNumber, io) =
print(io, "$(c.real)$(c.imag < 0 ? "-" : "+")$(abs(c.imag))i")

print_object.methods

c2 = new(ComplexNumber, real=3, imag=4)

c1
c2
add(c1,c2)

# Exemplo 2.6
class_of(c1) === ComplexNumber
ComplexNumber.direct_slots
class_of(class_of(c1)) === Class
class_of(class_of(class_of(c1))) === Class
Class.slots
ComplexNumber.name
ComplexNumber.direct_superclasses == [Object]
add
class_of(add) === GenericFunction
GenericFunction.slots
class_of(add.methods[1]) == MultiMethod
MultiMethod.slots
add.methods[1]
add.methods[1].generic_function === add

# Exemplo 2.7
@defclass(UndoableClass, [Class], [])
@defclass(Person, [],
[[name, reader=get_name, writer=set_name!],
[age, reader=get_age, writer=set_age!, initform=0],
[friend, reader=get_friend, writer=set_friend!]],
metaclass=UndoableClass)

Person
class_of(Person)
class_of(class_of(Person))

# Exemplo 2.8
P1 = new(Person, name="John", age=20)
get_age(P1)
set_age!(P1, 30)
get_name(P1)
set_name!(P1, "Mary")
get_friend(P1)
set_friend!(P1, P1)
#= These were the methods defined in the creation of the class
@defmethod get_name(o::Person) = o.name
@defmethod set_name!(o::Person, v) = o.name = v
@defmethod get_age(o::Person) = o.age
@defmethod set_age!(o::Person, v) = o.age = v
@defmethod get_friend(o::Person) = o.friend
@defmethod set_friend!(o::Person, v) = o.friend = v=#

# Exemplo 2.9
add(123,456)

# Exemplo 2.10

@defclass(Shape, [], [])
@defclass(Device, [], [])

@defgeneric draw(shape, device)

@defclass(Line, [Shape], [from, to])
@defclass(Circle, [Shape], [center, radius])

@defclass(Screen, [Device], [])
@defclass(Printer, [Device], [])

@defmethod draw(shape::Line, device::Screen) = println("Drawing a Line on Screen")
@defmethod draw(shape::Circle, device::Screen) = println("Drawing a Circle on Screen")
@defmethod draw(shape::Line, device::Printer) = println("Drawing a Line on Printer")
@defmethod draw(shape::Circle, device::Printer) = println("Drawing a Circle on Printer")

let devices = [new(Screen), new(Printer)],
    shapes = [new(Line), new(Circle)]
    for device in devices
        for shape in shapes
        draw(shape, device)
        end
    end
end

# Exemplo 2.11
@defclass(ColorMixin, [],
[[color, reader=get_color, writer=set_color!]])

@defmethod draw(s::ColorMixin, d::Device) =
    let previous_color = get_device_color(d)
        set_device_color!(d, get_color(s))
        call_next_method()
        set_device_color!(d, previous_color)
    end

@defclass(ColoredLine, [ColorMixin,Line], [])
@defclass(ColoredCircle, [ColorMixin,Circle], [])
@defclass(ColoredPrinter, [Printer],
[[ink=:black, reader=get_device_color, writer=_set_device_color!]])


@defmethod set_device_color!(d::ColoredPrinter, color) = begin
    println("Changing printer ink color to $color")
    _set_device_color!(d, color)
    end

let shapes = [new(Line), new(ColoredCircle, color=:red), new(ColoredLine, color=:blue)],
    printer = new(ColoredPrinter, ink=:black)
    for shape in shapes
        draw(shape, printer)
    end
end
        

# Exemplo 2.12
ColoredCircle.direct_superclasses
ans[1].direct_superclasses
ans[1].direct_superclasses
ans[1].direct_superclasses

# Exemplo 2.13
@defclass(A, [], [])
@defclass(B, [], [])
@defclass(C, [], [])
@defclass(D, [A, B], [])
@defclass(E, [A, C], [])
@defclass(F, [D, E], [])

compute_cpl(F)

# Exemplo 2.14
class_of(1)
class_of("Foo")

@defmethod add(a::_Int64, b::_Int64) = a + b
@defmethod add(a::_String, b::_String) = a * b
add.methods
add(1,3)
add("foo","bar")

# Exemplo 2.15
class_name(Circle)
class_direct_slots(Circle)
class_direct_slots(ColoredCircle)
class_slots(ColoredCircle)
class_direct_superclasses(ColoredCircle)
class_cpl(ColoredCircle)
generic_methods(draw)
method_specializers(generic_methods(draw)[1])

# Exemplo 2.16.1
@defclass(CountingClass, [Class],
[counter=0])

@defmethod allocate_instance(class::CountingClass) = begin
    class.counter += 1
    call_next_method()
end

@defclass(Foo, [], [], metaclass=CountingClass)
@defclass(Bar, [], [], metaclass=CountingClass)

new(Foo)
new(Foo)
new(Bar)

Foo.counter
Bar.counter

# Exemplo 2.16.2

@defclass(AvoidCollisionsClass, [Class], [])
@defmethod compute_slots(class::AvoidCollisionsClass) =
    let slots = call_next_method(),
        duplicates = symdiff(slots, unique(slots))
        isempty(duplicates) ?
        slots :
        error("Multiple occurrences of slots: $(join(map(string, duplicates), ", "))")
    end
    

@defclass(Foo, [], [a=1, b=2])
@defclass(Bar, [], [b=3, c=4])
@defclass(FooBar, [Foo, Bar], [a=5, d=6])
@defclass(FooBar2, [Foo, Bar], [a=5, d=6], metaclass=AvoidCollisionsClass)

# Exemplo 2.16.3
undo_trail = []

store_previous(object, slot, value) = push!(undo_trail, (object, slot, value))

current_state() = length(undo_trail)

restore_state(state) =
    while length(undo_trail) != state
        restore(pop!(undo_trail)...)
    end

save_previous_value = true

restore(object, slot, value) =
    let previous_save_previous_value = save_previous_value
        global save_previous_value = false
        try
            setproperty!(object, slot, value)
        finally
            global save_previous_value = previous_save_previous_value
        end
    end


@defclass(UndoableClass, [Class], [])

@defmethod compute_getter_and_setter(class::UndoableClass, slot, idx) =
    let (getter, setter) = call_next_method()
        (getter,
            (o, v)->begin
                    if save_previous_value
                        store_previous(o, slot, getter(o))
                    end
                    setter(o, v)
                end)
    end

@defclass(Person, [],
[name, age, friend],
metaclass=UndoableClass)

@defmethod print_object(p::Person, io) =
    print(io, "[$(p.name), $(p.age)$(ismissing(p.friend) ? "" : " with friend $(p.friend)")]")

p0 = new(Person, name="John", age=21)
p1 = new(Person, name="Paul", age=23)
p1.friend = p0
println(p1)
state0 = current_state()
p0.age = 53
p1.age = 55
p0.name = "Louis"
p0.friend = new(Person, name="Mary", age=19)
println(p1)
state1 = current_state()
p1.age = 70
p1.friend = missing
println(p1)
restore_state(state1)
println(p1)
restore_state(state0)
println(p1)

# Exemplo 2.16.4
@defclass(FlavorsClass, [Class], [])

@defmethod compute_cpl(class::FlavorsClass) = begin
    let depth_first_cpl(class) =
        [class, foldl(vcat, map(depth_first_cpl, class_direct_superclasses(class)), init=[])...],
            base_cpl = [Object, Top]
        vcat(unique(filter(!in(base_cpl), depth_first_cpl(class))), base_cpl)
    end
end

@defclass(A, [], [], metaclass=FlavorsClass)
@defclass(B, [], [], metaclass=FlavorsClass)
@defclass(C, [], [], metaclass=FlavorsClass)
@defclass(D, [A, B], [], metaclass=FlavorsClass)
@defclass(E, [A, C], [], metaclass=FlavorsClass)
@defclass(F, [D, E], [], metaclass=FlavorsClass)


compute_cpl(F)


# Exemplo 2.17
@defclass(UndoableCollisionAvoidingCountingClass,
[UndoableClass, AvoidCollisionsClass, CountingClass],
[])

@defclass(NamedThing, [], [name])

@defclass(Person, [NamedThing],
[name, age, friend],
metaclass=UndoableCollisionAvoidingCountingClass)
@defclass(Person, [NamedThing],
[age, friend],
metaclass=UndoableCollisionAvoidingCountingClass)

@defmethod print_object(p::Person, io) =
print(io, "[$(p.name), $(p.age)$(ismissing(p.friend) ? "" : " with friend $(p.friend)")]")

p0 = new(Person, name="John", age=21)
p1 = new(Person, name="Paul", age=23)
p1.friend = p0
println(p1)
state0 = current_state()
p0.age = 53
p1.age = 55
p0.name = "Louis"
p0.friend = new(Person, name = "Mary", age = 19)
println(p1)
state1 = current_state()
p1.age = 70
p1.friend = missing
println(p1)
restore_state(state1)
println(p1)
restore_state(state0)
println(p1)

Person.counter







    
