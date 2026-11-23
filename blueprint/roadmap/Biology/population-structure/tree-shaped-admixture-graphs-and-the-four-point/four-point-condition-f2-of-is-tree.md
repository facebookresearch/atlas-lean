# f2 satisfies the four-point condition on a tree-shaped admixture graph

Let `G` be a [tree-shaped](../admixture-graphs/is-tree.md)
[admixture graph](../admixture-graphs/admixture-graph.md) on a finite set of nodes, and let `M` be a
[drift model](../patterson-s-f-statistics/drift-model.md) on any measure space whose populations are
the nodes of `G`, whose edges are the [edges](../admixture-graphs/edge.md) of `G` and whose lineage
weights are the [lineage weights](../admixture-graphs/weight.md) of `G`. Then the
[f2 statistic](../patterson-s-f-statistics/f2.md) of its population frequencies satisfies the
[four-point condition](../../../GraphTheory/graph-families-and-operations/tree-metrics-and-the-four-point-condition/four-point-condition.md):
`f2(x, y) + f2(z, t) ≤ max(f2(x, z) + f2(y, t), f2(x, t) + f2(y, z))` for all nodes `x, y, z, t`.
Binary loadings alone do not suffice: four populations with weight vectors `00, 10, 01, 11` on two
edges of positive length have binary loadings, but their `f2` violates the condition. Here the
lineages are root-ward paths of one tree, so the edges cannot split a quartet in
[two different ways](quartet-compatible-of-is-tree.md).
