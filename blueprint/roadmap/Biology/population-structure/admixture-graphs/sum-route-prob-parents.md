# Off the root, routing probabilities over parent assignments sum to one

In every [admixture graph](admixture-graph.md) with root `ρ` and parent sets `pa`, for every node
`X ≠ ρ` and every natural number `k`, the [routing probabilities](route-prob.md) of the
assignments of the `k` lineages to parents of `X` sum to one: `∑_y R(X, y) = 1`, the sum running
over the maps `y` from `{0, …, k - 1}` to `pa(X)`. Indeed the sum factors as
`(∑_{Y ∈ pa(X)} a(X, Y))^k = 1`. For `k = 0` the only assignment is the empty one, of
probability `1`. The set of nodes need not be finite.
