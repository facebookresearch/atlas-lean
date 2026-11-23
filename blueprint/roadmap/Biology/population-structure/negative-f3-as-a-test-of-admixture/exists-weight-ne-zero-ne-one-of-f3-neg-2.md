# On an admixture graph a negative f3 forces a non-binary target weight

Let `G` be an [admixture graph](../admixture-graphs/admixture-graph.md) on a finite set of nodes and
`M` a [drift model](../patterson-s-f-statistics/drift-model.md) on the
[edges](../admixture-graphs/edge.md) of `G` whose lineage weights are the
[lineage weights](../admixture-graphs/weight.md) `w` of `G`. If `f3(C; A, B) < 0` for the
[f3 statistic](../patterson-s-f-statistics/f3.md) of the population frequencies of `M`, then some
edge `e` has `w(C, e) ≠ 0` and `w(C, e) ≠ 1`: the target `C` does not have the binary weights of an
unadmixed population. This is the contrapositive of the
[nonnegative f3 of a target with binary weights](f3-nonneg-of-binary-weights.md).
