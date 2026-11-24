# DC nodal injection

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e` and real node phase angles `θ_v`. The DC nodal injection is the vector
`p = B f`, where `f` is the [DC branch flow](dc-branch-flow.md) and `B` the
[electrical incidence](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md),
`B_{ve} = [t(e) = v] - [h(e) = v]`. At node `v`,

`p_v = ∑_{e : t(e) = v} f_e - ∑_{e : h(e) = v} f_e`,

the flow leaving `v` on the branches with tail `v` minus the flow arriving on the branches with head
`v` (a loop at `v` enters both sums and cancels). It is read as the net real power injected into the
network at `v`. In the physical reading the susceptances are positive; the definition allows all
real `b` and `θ`.
