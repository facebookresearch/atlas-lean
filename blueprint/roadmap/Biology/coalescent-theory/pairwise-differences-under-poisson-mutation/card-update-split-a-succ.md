# A single choice of step $t$ merges $b$ with $c$ while $a$ stays apart

Let `t < n - 1`, let `a`, `b`, `c` be genes and `f` a [ranked labeled history](../ranked-labeled-histories-of-coalescent-trees/ranked-history.md) of `n` genes in which `a`, `b`, `c`
are in [three distinct lineages](apart3.md) after `t` events. Exactly one of the `C(n - t, 2)`
[pairs](../ranked-labeled-histories-of-coalescent-trees/lineage-pair.md) `x` of the `n - t` lineages at step `t` gives a history `f[t ↦ x]` (the history `f` with
step `t` replaced by `x`) in which `a`, `b`, `c` are in three distinct lineages after `t` events
and, after `t + 1` events, [`a` is apart from `b` and `c` while `b` and `c` share a lineage](split-a.md):
the pair of lineages of `b` and `c`.
