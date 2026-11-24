# On an admixture graph a target with binary weights has nonnegative f3

Let `G` be an [admixture graph](../admixture-graphs/admixture-graph.md) on a finite set of nodes and
`M` a [drift model](../patterson-s-f-statistics/drift-model.md) on the
[edges](../admixture-graphs/edge.md) of `G` whose lineage weights are the
[lineage weights](../admixture-graphs/weight.md) `w` of `G`. If every weight `w(C, e)` of a node `C`
is `0` or `1`, then `f3(C; A, B) ≥ 0` for all nodes `A`, `B`, possibly admixed, for the
[f3 statistic](../patterson-s-f-statistics/f3.md) of the population frequencies of `M`. No condition
on the sources is needed, since lineage weights of a graph always lie in `[0, 1]`
([nonnegative](../admixture-graphs/weight-nonneg.md),
[at most one](../admixture-graphs/weight-le-one.md)).
