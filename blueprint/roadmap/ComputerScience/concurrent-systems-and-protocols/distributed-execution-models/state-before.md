# State Before

The local state just before tick `t`, computed from the initial state and the recorded
successors at previous ticks. A tick with no step by `p` does not change its state. On a legal
history there is at most one step by `p` per tick, so this is also its state before that step.
