# All but one choice of step $t$ keep an apart pair apart

Let `t < n - 1`, let `a` and `b` be genes and `f` a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes in which `{a, b}` is
[apart](pair-apart.md) after `t` events. Of the `C(n - t, 2)` [pairs](../ranked-labeled-histories-of-coalescent-trees/lineage-pair.md) `x` of the `n - t` lineages at step `t`,
exactly `C(n - t, 2) - 1` keep `{a, b}` apart after `t + 1` events of `f[t ↦ x]`, the history
`f` with step `t` replaced by `x`: all but the pair of lineages of `a` and `b`.
