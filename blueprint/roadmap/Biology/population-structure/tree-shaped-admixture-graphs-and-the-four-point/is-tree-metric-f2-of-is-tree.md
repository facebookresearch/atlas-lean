# f2 is a tree metric on a tree-shaped admixture graph

Let `G` be a [tree-shaped](../admixture-graphs/is-tree.md)
[admixture graph](../admixture-graphs/admixture-graph.md) on a finite set of nodes, and let `M` be a
[drift model](../patterson-s-f-statistics/drift-model.md) on any measure space whose populations are
the nodes of `G`, whose edges are the [edges](../admixture-graphs/edge.md) of `G` and whose lineage
weights are the [lineage weights](../admixture-graphs/weight.md) of `G`. Then the
[f2 statistic](../patterson-s-f-statistics/f2.md) of its population frequencies is a
[tree metric](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric.md):
there are a finite tree with positive edge lengths and a placement of the nodes of `G` on its
vertices such that `f2(x, y)` is the length of the path between the vertices of `x` and `y`. This
follows from [the four-point condition for f2](four-point-condition-f2-of-is-tree.md) and
[Buneman's theorem](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/is-tree-metric-of-four-point-condition.md),
since `f2(x, x) = 0` and `f2(x, y) = f2(y, x)`.
