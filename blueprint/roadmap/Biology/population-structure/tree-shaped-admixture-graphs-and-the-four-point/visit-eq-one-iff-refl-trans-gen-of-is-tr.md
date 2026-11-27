# On a tree a lineage passes through exactly the node and its ancestors

In an [admixture graph](../admixture-graphs/admixture-graph.md) that is
[tree-shaped](../admixture-graphs/is-tree.md), the [visit probability](../admixture-graphs/visit.md)
satisfies `v(X, c) = 1` if and only if `c` is `X` or an ancestor of `X`, that is, `c` is reached
from `X` by passing from a node to its parent zero or more times. On a tree every visit probability
is [zero or one](../admixture-graphs/visit-eq-zero-or-one.md), so `v(X, c) = 0` for every other node
`c`.
