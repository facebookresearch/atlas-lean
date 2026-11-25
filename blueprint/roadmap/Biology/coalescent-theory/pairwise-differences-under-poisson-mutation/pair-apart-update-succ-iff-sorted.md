# Apartness after replacing step $t$, for genes in distinct lineages

Let `f` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes and `t < n - 1`, and let `pos` give the label of the lineage that
holds each gene after `t` events of `f` (the [position map](is-block-partition.md) of the blocks
after `t` events). For a [pair of lineages](../ranked-labeled-histories-of-coalescent-trees/lineage-pair.md) `x` among the `n - t` lineages and genes `u` and `v` with
`pos u ≠ pos v`, `{u, v}` is [apart](pair-apart.md) after `t + 1` events of `f[t ↦ x]`, the history `f` with step `t` replaced by `x`, if and only if the
[smaller](pair-lo.md) and [larger](pair-hi.md) labels `(lo, hi)` of `x` differ from
`(min(pos u, pos v), max(pos u, pos v))`.
