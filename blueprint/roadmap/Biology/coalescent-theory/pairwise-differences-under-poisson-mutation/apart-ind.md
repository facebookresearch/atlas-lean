# Indicator that a set of genes is apart after $u$ events

For a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h` of `n` genes, a set `s` of sampled genes and a natural number `u`, the real number
`1[s apart after u]`: it is `1` if, after the first `u` coalescence events of `h`, no lineage
contains all the genes of `s` (`s` is [apart](pair-apart.md)), and `0` otherwise. For a pair `s = {a, b}` of
distinct genes it is `1` exactly when `a` and `b` are in different lineages. For `n ≥ 1` it is
`0` for a set of at most one gene, and `0` for every `s` once `u ≥ n - 1`, when one lineage holds
all the genes; for `n = 0` it is `1` at every `u`, the only set, the empty set, being vacuously
apart.
