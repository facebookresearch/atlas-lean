# Indicator that a set of genes is apart after $u$ events

For a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) `h` of `n` genes, a set `s` of sampled genes and a natural number `u`, the real number
`1[s apart after u]`: it is `1` if, after the first `u` coalescence events of `h`, no lineage
contains all the genes of `s` (`s` is [apart](pair-apart.md)), and `0` otherwise. For a pair `s = {a, b}` of
distinct genes it is `1` exactly when `a` and `b` are in different lineages.
