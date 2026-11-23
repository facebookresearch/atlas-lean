# Genes are together after a step iff together before or merged by it

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes, `t < n - 1` a step, and `pos` a map for which the
[lineage blocks after the first `t` events](../ranked-labeled-histories-of-coalescent-trees/blocks-after.md)
form a [block partition](is-block-partition.md) with positions `pos`. Let `{u, v}`, with
`u < v`, be the pair of lineages that `h` records at step `t`. Then for all genes `a` and `b`,
the pair `{a, b}` is [apart](pair-apart.md) after `t + 1` events if and only if neither
`pos a = pos b` nor `{pos a, pos b} = {u, v}`: the two genes are in one lineage after `t + 1`
events exactly when they were in one lineage after `t` events or step `t` merges their two
lineages.
