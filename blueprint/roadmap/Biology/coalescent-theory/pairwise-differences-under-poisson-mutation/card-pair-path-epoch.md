# Two branches per epoch separate a pair while apart, none afterwards

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n`
genes, `a ≠ b` distinct genes and `k` an epoch, `2 ≤ k ≤ n`. The number of
[branches](../poisson-mutation-on-the-kingman-genealogy/kingman-branch.md) of epoch `k` (the lineages
`j < k` while there are `k` lineages) with exactly one of `a` and `b`
[below them](branch-block.md) is `2` if the pair `{a, b}` is [apart](pair-apart.md) after the
first `n - k` coalescence events, that is, in different lineages during epoch `k`, and `0`
otherwise.
