# Decides

Process `p` decides `v` at tick `t` when a `deliver p r v` occurs after an actual local
`propose` and no earlier delivery to `p` occurred after a local proposal. No correctness premise
restricts `p`. Figure 6 initialises the handler inside `propose`; it does not specify behaviour
before invocation. Here an early R-delivery is ignored locally and is not replayed. Later
R-deliveries after a first decision are ignored for decision only. Program prefixes model one
invocation at most per process; even on a raw stream a second proposal cannot re-arm the guard.
