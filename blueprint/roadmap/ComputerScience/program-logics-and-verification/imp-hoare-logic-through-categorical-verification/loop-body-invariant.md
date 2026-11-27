# A loop invariant gives the categorical loop-body specification

If the IMP command `c` is valid for precondition `I ∧ b` and postcondition
`I`, then the loop body of `while b do c` satisfies the tensor triple of the
powerset verification structure from the pair of `I`-states to the pair
consisting of the `I`-states where `b` is false and the `I`-states.
