# Exactly one choice of step $t$ merges two genes that are apart

Let `t < n - 1`, let `u` and `v` be genes, let `f` be a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes in which `{u, v}` is
[apart](pair-apart.md) after `t` events, and let `Q` be a property of histories that `f` has and that does not
change when step `t` of `f` is replaced by any [pair of lineages](../ranked-labeled-histories-of-coalescent-trees/lineage-pair.md). Exactly one of the `C(n - t, 2)` pairs `x`
of the `n - t` lineages at step `t` gives a history `f[t ↦ x]` (the history `f` with step `t`
replaced by `x`) that has `Q` and in which `u` and `v` share a lineage after `t + 1` events: the
pair of lineages of `u` and `v`.
