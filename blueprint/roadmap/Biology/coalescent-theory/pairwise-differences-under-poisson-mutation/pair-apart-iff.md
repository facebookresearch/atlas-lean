# Two genes are apart exactly when their block positions differ

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes, `t` a natural number and `pos` a map for which the
[lineage blocks after the first `t` coalescence events](../ranked-labeled-histories-of-coalescent-trees/blocks-after.md)
form a [block partition](is-block-partition.md) with positions `pos`. Then for all genes `a` and
`b`, the pair `{a, b}` is [apart](pair-apart.md) after `t` events if and only if
`pos a ≠ pos b`.
