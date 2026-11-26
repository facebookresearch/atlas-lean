# Finite executions of an asynchronous message-passing system

`π.IsExecution C₀ φs C Cs`
says that the configurations `Cs = [C₀, C₁, …, Cₙ]`, with `Cₙ = C`, and the events
`φs = [φ₁, …, φₙ]` form an execution of `π`: `C₀` is initial and each `Cₖ₊₁` results from
applying `φₖ₊₁` to `Cₖ`, as a transition of `π.lts`.
