# On a tree edges on a common lineage are traversed by nested sets

In an [admixture graph](../admixture-graphs/admixture-graph.md) that is
[tree-shaped](../admixture-graphs/is-tree.md), let the lineage of a node `X` traverse two
[edges](../admixture-graphs/edge.md) `e` and `f`, that is, `w(X, e) = w(X, f) = 1` for the
[lineage weights](../admixture-graphs/weight.md) `w`. Then either every lineage that traverses `e`
also traverses `f` (`w(Y, e) = 1` implies `w(Y, f) = 1` for every node `Y`), or every lineage that
traverses `f` also traverses `e`: the sets of nodes whose lineages traverse `e` and `f` are nested.
