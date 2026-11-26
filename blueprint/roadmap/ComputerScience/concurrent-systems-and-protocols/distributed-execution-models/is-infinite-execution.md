# Infinite executions of an asynchronous message-passing system

The configurations `Cs`
and the events `φs` form an infinite execution of `π` if `Cs 0` is initial and, for every `n`, the
event `φs n` can occur in `Cs n` and `Cs (n + 1)` results from applying it, as a transition of
`π.lts`. An event of process `p` can occur in a configuration if, for every process `i`, the
messages it delivers from `i` are in the channel `chan i p`, with multiplicity. Applying it removes
them from these channels, gives `p` the state its transition function assigns to its current state
and the messages delivered, and adds each message that the transition function sends to the
channel from `p` to its recipient.
