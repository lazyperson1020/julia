#!/usr/bin/env -S julia --project=@scriptdir

module Main2

using Core: OpaqueClosure
using Base: @ccallable
using Base.Experimental: @opaque

mutable struct TypedCallable{AT,RT} <: Function
    oc::OpaqueClosure{AT,RT}
    const task::Task

    function TypedCallable(oc::OpaqueClosure{AT,RT}) where {AT,RT}
        # TODO: investigate _terrible_ stack trace without this type ascription...
        #
        #ERROR: Dynamic call to Base.convert(Type{Main2.TypedCallable{Tuple{Float64}, Float64}}, Function)
        # In array.jl:1262
        # Stacktrace:
        #  [1] push!(a::Array{TypedCallable{Tuple{Float64}, Float64}, 1}, item::Function)
        #    @ Base array.jl:1262
        #  [2] main()
        #    @ Main2 ~/repos/dae_julia/juliac/exe_examples/opaque_closure.jl:71
        return new{AT,RT}(oc, Base.current_task()::Task)
    end
end

function Base.convert(::Type{TypedCallable{AT,RT}}, oc::OpaqueClosure{AT,RT}) where {AT,RT}
    return TypedCallable(oc)
end

function rebuild!(@nospecialize(self::TypedCallable))
   world = Base.tls_world_age()
   source = self.oc.source
   captures = self.oc.captures
   do_compile = true
   AT, RT = typeof(self).parameters
   self.oc = ccall(:jl_new_opaque_closure, Any,
       (Any, Any, Any,    Any,      Any, Csize_t,       Cint),
         AT,  RT,  RT, source, captures,   world, do_compile
   )::OpaqueClosure{AT,RT}
   return nothing
end

function (self::TypedCallable{AT,RT})(args...) where {AT,RT}
    if Base.current_task() !== self.task
        error("TypedCallable{...} was called from a different task than it was created in.")
    end
    # TODO: Is this code structure sufficient for LLVM to elide the world age saving?
    while self.oc.world != Base.tls_world_age()
        rebuild!(self)
    end
    return self.oc(args...)
end

function make_offset_func(y::Float64)
    # why does the implicit convert here not work?
    return (@opaque (x::Float64)->(x + y))::OpaqueClosure{Tuple{Float64}, Float64}
end

@noinline function run_all(callables)
    input = rand(Float64)
    println(Core.stdout, "test input: ", string(input))
    for (i, f) in enumerate(callables)
        result = f(input)
        println(Core.stdout, "callable #", string(i), " gave result: ", string(result))
    end
end

const OC = OpaqueClosure{Tuple{Float64},Float64}

@ccallable function main()::Cint

    oc = @noinline make_offset_func(1.5)
    println(Core.stdout, "got: ", string(oc(1.5)))

    # TODO: solve this mystery?
    # callables = OpaqueClosure{Tuple{Float64},Float64}[]
    callables = TypedCallable{Tuple{Float64},Float64}[]
    push!(callables, make_offset_func(1.0))
    push!(callables, make_offset_func(2.5))
    push!(callables, (@opaque (x::Float64)->2x)::OC)
    push!(callables, (@opaque (x::Float64)->begin
        println(Core.stdout, "Got argument: ", string(x))
        return x
    end)::OC)

    run_all(callables)

    return 0
end

end
