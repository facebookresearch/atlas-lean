# Profile hidden Markov model

A profile HMM with `L` consensus columns over the alphabet `α`, with weights in `R`.
`trans k s t` is the weight of a transition from the state of type `s` at node `k`
(`0 ≤ k ≤ L`; node `0` is the begin state, read as type `M`) to a state of type `t`: to `M`
or `D` at node `k + 1`, or to `I` at node `k`. `stop s` is the weight of the transition from the
state of type `s` at node `L` to the end state.
