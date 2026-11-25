# On a tree lineage visits are transitive

In an [admixture graph](../admixture-graphs/admixture-graph.md) that is
[tree-shaped](../admixture-graphs/is-tree.md), if the lineage of `X` passes through `c` and the
lineage of `c` passes through `d`, that is, `v(X, c) = 1` and `v(c, d) = 1` for the
[visit probability](../admixture-graphs/visit.md) `v`, then the lineage of `X` passes through `d`:
`v(X, d) = 1`.
