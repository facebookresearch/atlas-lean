# Sending a lineage to a non-parent has routing probability zero

In every [admixture graph](admixture-graph.md) with parent sets `pa`, let `X` be a node (the root
included) and `y` an assignment of `k` lineages to nodes. If some lineage `i` is sent to a node
`y_i ∉ pa(X)` that is not a parent of `X`, then the [routing probability](route-prob.md) is
`R(X, y) = 0`, since its factor `a(X, y_i)` vanishes.
