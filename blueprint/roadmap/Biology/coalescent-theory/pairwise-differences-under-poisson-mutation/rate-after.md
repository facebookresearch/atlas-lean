# Coalescence rate after $u$ coalescence events

For natural numbers `n` and `u`, the real number `C(n - u, 2)`, where the subtraction `n - u` is
truncated at `0`. For `n ≥ 1` and `u ≤ n - 1`, a sample of `n` genes has `n - u` lineages after
`u` coalescence events, and `C(n - u, 2)` is the number of pairs among them, which is the total
coalescence rate of Kingman's coalescent with that many lineages. It is positive for `u + 2 ≤ n`,
that is, at the steps `u < n - 1` of a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md),
and, for `n ≥ 1`, it is `0` at `u = n - 1`, when one lineage is left. For `u ≥ n` the rate is
`0`. If `n ≥ 1`, the truncated `n - u = 0` is then not the number of lineages: the single final
lineage remains, since the history has only `n - 1` events. If `n = 0` there are no lineages at
all, and `n - u = 0` is their number.
