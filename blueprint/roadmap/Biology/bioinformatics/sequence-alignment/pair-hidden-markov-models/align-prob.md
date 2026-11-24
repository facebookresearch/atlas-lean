# Joint weight of sequences and an alignment's state path

For a pair HMM with weights in a semiring and an [alignment](../pairwise-sequence-alignment/alignment.md) $A$, the joint weight is the [weight](align-weight.md) of $A$ read from the begin state by the [associated automaton](to-automaton.md): the product of the transition and emission weights along the state path visiting the state of each column, from the begin state to the end state.
