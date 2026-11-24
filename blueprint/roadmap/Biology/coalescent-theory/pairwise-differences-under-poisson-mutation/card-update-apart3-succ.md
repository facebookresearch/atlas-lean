# All but three choices of step $t$ keep three distinct lineages apart

Let `t < n - 1`, let `a`, `b`, `c` be genes and `f` a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes in which `a`, `b`, `c`
are in [three distinct lineages](apart3.md) after `t` events. Of the `C(n - t, 2)` [pairs](../ranked-labeled-histories-of-coalescent-trees/lineage-pair.md) `x` of
the `n - t` lineages at step `t`, exactly `C(n - t, 2) - 3` keep them in three distinct lineages
after `t + 1` events of `f[t ↦ x]`, the history `f` with step `t` replaced by `x`: all but the
three pairs formed by their lineages.
