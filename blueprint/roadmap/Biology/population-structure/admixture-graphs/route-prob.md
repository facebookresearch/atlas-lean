# Routing kernel for several lineages at a node

Let `G` be an [admixture graph](admixture-graph.md) on a set `V` of nodes, with parent sets `pa`
and admixture proportions `a`. For a node `X`, a natural number `k` and an assignment
`y = (y_0, …, y_{k-1})` of `k` lineages to nodes, the routing probability is the product
`R(X, y) = ∏_{i < k} a(X, y_i)`. It describes `k` lineages at `X`, traced backward in time, that
move to parents independently, lineage `i` to `y_i` with probability `a(X, y_i)`; as
`a(X, Y) = 0` unless `Y ∈ pa(X)`, only assignments to parents of `X` can have nonzero probability.
For `k = 0` the product is empty and the single empty assignment has probability `1`, at every
node. At a node `X` other than the root the routing probabilities sum to one over the
[assignments to parents](sum-route-prob-parents.md) and, for finitely many nodes, over
[all assignments](sum-route-prob.md); at the root, which has no parents, every assignment of
`k > 0` lineages [has probability `0`](route-prob-root.md).
