# Bar Tuple degen

Bar-side degeneracy tuple formula.

`barTuple` of a degeneracy inserts `1` head-first: unfold `σ i` to
`barEtaAtPos` (`barData_σ_app`), read both sides through the generalized
reader, and apply `genEtaFst`. The public `barEtaAtPos` wrapper counts from
the right-module end, so `i.rev` restores the head-first tuple position `i`
(`n - (n - i) = i`). No induction here.
