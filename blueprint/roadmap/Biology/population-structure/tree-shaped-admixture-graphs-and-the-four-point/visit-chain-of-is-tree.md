# On a tree two nodes on one lineage are comparable

In an [admixture graph](../admixture-graphs/admixture-graph.md) that is
[tree-shaped](../admixture-graphs/is-tree.md), if the lineage of `X` passes through both `c` and
`d`, that is, `v(X, c) = v(X, d) = 1` for the [visit probability](../admixture-graphs/visit.md) `v`,
then one of the two nodes lies on the lineage of the other: `v(c, d) = 1` or `v(d, c) = 1`.
