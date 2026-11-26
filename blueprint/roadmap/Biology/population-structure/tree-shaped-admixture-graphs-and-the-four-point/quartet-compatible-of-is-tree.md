# On a tree no quartet is split by edges in two different ways

In an [admixture graph](../admixture-graphs/admixture-graph.md) that is
[tree-shaped](../admixture-graphs/is-tree.md), with [lineage weights](../admixture-graphs/weight.md)
`w`, for all nodes `x, y, z, t` either `(w(x, e) - w(t, e)) (w(y, e) - w(z, e)) ≥ 0` for every
[edge](../admixture-graphs/edge.md) `e`, or `(w(x, e) - w(z, e)) (w(y, e) - w(t, e)) ≥ 0` for every
edge `e`. Since the weights are `0` or `1`, the first product is negative exactly on the `xz | yt`
edges, those traversed, among the lineages of `x, y, z, t`, by exactly those of `x` and `z` or by
exactly those of `y` and `t`, and the second exactly on the `xt | yz` edges, defined likewise; so no
tree has edges of both kinds. In a drift model with these weights and drift lengths `ℓ`, the sums
`∑ e` of these products times `ℓ(e)` are half the pair-sum differences
`f2(x, z) + f2(y, t) - f2(x, y) - f2(z, t)` and `f2(x, t) + f2(y, z) - f2(x, y) - f2(z, t)` that
enter the [four-point condition](four-point-condition-f2-of-is-tree.md).
