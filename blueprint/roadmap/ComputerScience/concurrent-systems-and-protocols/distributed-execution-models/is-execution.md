# Finite executions of an asynchronous message-passing system

`π.IsExecution C₀ φs C Cs`
says that the configurations `Cs = [C₀, C₁, …, Cₙ]`, with `Cₙ = C`, and the events
`φs = [φ₁, …, φₙ]` form an execution of `π`: `C₀` is initial, and each event `φₖ₊₁` can occur in
`Cₖ` and `Cₖ₊₁` results from applying it, as a transition of `π.lts`. An event of process `p` can
occur in a configuration if, for every process `i`, the messages it delivers from `i` are in the
channel `chan i p`, with multiplicity. Applying it removes them from these channels, gives `p` the
state its transition function assigns to its current state and the messages delivered, and adds
each message that the transition function sends to the channel from `p` to its recipient.
