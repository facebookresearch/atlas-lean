# On a tree an edge weight is the visit probability of its child end

In an [admixture graph](../admixture-graphs/admixture-graph.md) that is
[tree-shaped](../admixture-graphs/is-tree.md), for every node `X` and every
[edge](../admixture-graphs/edge.md) `e = (c, p)` from a child `c` to its parent `p`, the
[lineage weight](../admixture-graphs/weight.md) equals the
[visit probability](../admixture-graphs/visit.md) of the child end: `w(X, e) = v(X, c)`. So the
probability that the lineage of `X` traverses `e` equals the probability that it passes through `c`.
