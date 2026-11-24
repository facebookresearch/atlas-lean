# Routing kernel rows at non-root nodes sum to one

In every [admixture graph](admixture-graph.md) on a finite set `V` of nodes with root `ρ`, for every
node `X ≠ ρ` and every natural number `k`, the [routing probabilities](route-prob.md) of all
assignments of `k` lineages to nodes sum to one: `∑_y R(X, y) = 1`, the sum running over all maps
`y` from `{0, …, k - 1}` to `V`. The assignments that send a lineage outside the parents of `X`
[contribute `0`](route-prob-eq-zero.md), so this extends the
[sum over parent assignments](sum-route-prob-parents.md) to all maps: at every non-root node the
routing probabilities form a probability distribution on the assignments.
