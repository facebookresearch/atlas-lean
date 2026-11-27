# All but six choices of step $t$ keep four distinct lineages apart

Let `t < n - 1`, let `a`, `b`, `c`, `d` be genes and `f` a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes in which they are in
[four distinct lineages](apart4.md) after `t` events. Of the `C(n - t, 2)` [pairs](../ranked-labeled-histories-of-coalescent-trees/lineage-pair.md) `x` of the
`n - t` lineages at step `t`, exactly `C(n - t, 2) - 6` keep them in four distinct lineages after
`t + 1` events of `f[t ↦ x]`, the history `f` with step `t` replaced by `x`: all but the six
pairs formed by their lineages.
