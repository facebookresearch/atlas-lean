# Weight of a path through a profile HMM

The weight of a path, given as an alignment of a sequence to the [columns](columns.md), is its [weight](../pair-hidden-markov-models/align-weight.md) read from the control state $(M, 0)$ by the [associated automaton](to-automaton.md): the product of its transition and emission weights from the begin state to the end state.
