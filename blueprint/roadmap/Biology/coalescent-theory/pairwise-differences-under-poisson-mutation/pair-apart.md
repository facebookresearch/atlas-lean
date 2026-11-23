# Genes apart after $t$ events: no lineage block contains them all

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes, `s` a set of sampled genes and `t` a natural number. The genes of `s` are apart after `t`
events when no block in the list of
[lineage blocks after the first `t` coalescence events](../ranked-labeled-histories-of-coalescent-trees/blocks-after.md)
of `h` contains all of `s`: the genes of `s` are not all in one lineage. It is meant for a pair
`s = {a, b}` of distinct genes, where it says that `a` and `b` are still in different lineages.
When `n ≥ 1`, a set of at most one gene is never apart, since some block contains it.
