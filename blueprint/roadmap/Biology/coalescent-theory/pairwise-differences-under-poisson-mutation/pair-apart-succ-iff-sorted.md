# Genes in distinct lineages stay apart unless step $t$ joins them

Let `h` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes and `t < n - 1`, and let `pos` give the label of the lineage that
holds each gene after `t` events of `h` (the [position map](is-block-partition.md) of the blocks
after `t` events). For genes `u` and `v` with `pos u ≠ pos v`, `{u, v}` is [apart](pair-apart.md) after
`t + 1` events if and only if the pair merged at step `t`, written `(lo, hi)` with its
[smaller](pair-lo.md) and [larger](pair-hi.md) label, differs from
`(min(pos u, pos v), max(pos u, pos v))`.
