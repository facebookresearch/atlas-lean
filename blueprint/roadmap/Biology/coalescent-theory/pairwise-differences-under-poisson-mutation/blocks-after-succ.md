# Each coalescence event merges the two blocks of the pair it records

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes, let `t < n - 1` be a step, and let `{u, v}`, with `u < v`, be the pair of lineages that
`h` records at step `t`. Then the
[lineage blocks after the first `t + 1` coalescence events](../ranked-labeled-histories-of-coalescent-trees/blocks-after.md)
of `h` are obtained from the blocks after the first `t` events by
[merging the blocks](../ranked-labeled-histories-of-coalescent-trees/merge-blocks.md) at positions `u` and
`v`.
