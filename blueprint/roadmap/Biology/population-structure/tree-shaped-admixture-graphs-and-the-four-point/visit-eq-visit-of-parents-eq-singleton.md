# A node with a single parent visits other nodes as its parent does

In every [admixture graph](../admixture-graphs/admixture-graph.md), if a node `X` has the single
parent `Y`, `parents(X) = {Y}`, then for every node `c ≠ X` the
[visit probabilities](../admixture-graphs/visit.md) agree, `v(X, c) = v(Y, c)`: the lineage of `X`
moves to `Y` with probability `1`, so it passes through `c` with the same probability as the lineage
of `Y`. No tree assumption is needed. For `c = X` the two sides are `1` and `0`.
