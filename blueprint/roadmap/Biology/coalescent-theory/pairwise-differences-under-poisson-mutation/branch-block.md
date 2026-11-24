# Sampled genes below a branch of the genealogy

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes and `(k, j)` a [branch](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) of the
genealogy: the branch of lineage `j < k` during the epoch with `k` lineages, `2 ≤ k ≤ n`. The
genes below the branch are the block at position `j` in the list of
[lineage blocks after the first `n - k` coalescence events](../ranked-labeled-histories-of-coalescent-trees/blocks-after.md)
of `h`. That list has exactly `k` blocks ([block count](blocks-after-spec.md)), so this block
always exists.
