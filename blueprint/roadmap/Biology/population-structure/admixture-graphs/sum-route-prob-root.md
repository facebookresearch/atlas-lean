# With at least one lineage, the routing kernel's root row has mass zero

In every [admixture graph](admixture-graph.md) on a finite set `V` of nodes with root `ρ`, for every
natural number `k > 0`, the [routing probabilities](route-prob.md) at the root sum to zero over all
assignments of `k` lineages to nodes: `∑_y R(ρ, y) = 0`, the sum running over all maps `y` from
`{0, …, k - 1}` to `V`, as [every term is `0`](route-prob-root.md). So for `k > 0` the root row is
not a probability distribution; the routing probabilities form one at every
[non-root node](sum-route-prob.md) and, for `k = 0`, at every node, where the single empty
assignment has [probability `1`](route-prob-zero.md).
