# The DC injection is the weighted Laplacian applied to the angles

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed). For all real
branch susceptances `b_e` and node phase angles `θ_v`, the [DC nodal injection](dc-injection.md) is

`p = B f = L_b θ`,

where `f` is the [DC branch flow](dc-branch-flow.md), `B` the
[electrical incidence](../../circuit-theory/tellegen-s-theorem-and-branch-power-balance/electrical-incidence.md)
and `L_b = B diag(b) Bᵀ` the full [susceptance-weighted Laplacian](weighted-laplacian.md). In the
physical reading the susceptances are positive; the identity holds for all real `b`.
