# Profile HMM as an alignment automaton

The profile HMM as an alignment automaton reading alignments of a sequence to the columns
`[1, …, L]`. The control state is the type of the previous state and the current node (the last
column consumed); it starts at `(M, 0)`, the begin state. Reading `(some a, some j)` visits `M j`,
`(some a, none)` visits the insert state of the current node, `(none, some j)` visits `D j`; the
invalid column `(none, none)` has weight `0`.
