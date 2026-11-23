# Coalescence rate after $u$ coalescence events

For natural numbers `n` and `u`, the real number `C(n - u, 2)`, where the subtraction `n - u` is
truncated at `0`. For `n ≥ 1` and `u ≤ n - 1`, a sample of `n` genes has `n - u` lineages after
`u` coalescence events, and `C(n - u, 2)` is the number of pairs among them, which is the total
coalescence rate of Kingman's coalescent with that many lineages. It is positive for `u + 2 ≤ n`,
that is, at the steps `u < n - 1` of a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md),
and `0` at `u = n - 1`, when one lineage is left. For `u ≥ n` the value is `0` as well, but the
truncated `n - u = 0` is not the number of lineages: for `n ≥ 1` the single final lineage
remains, since the history has only `n - 1` events (for `n = 0` there are no lineages at all).
