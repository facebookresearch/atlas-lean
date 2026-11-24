# DC branch flow

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e` and real node phase angles `θ_v`. The DC branch flow is the vector

`f = diag(b) Bᵀ θ`,

where `B` is the
[electrical incidence](../../circuit-theory/tellegen-s-theorem-and-branch-power-balance/electrical-incidence.md),
`B_{ve} = [t(e) = v] - [h(e) = v]` (`1` at the tail, `-1` at the head, a zero column for a loop).
Componentwise [`f_e = b_e (θ_{t(e)} - θ_{h(e)})`](dc-branch-flow-apply.md), read as the real power
flowing through branch `e` from its tail to its head. In the physical reading the susceptances are
positive; the definition allows all real `b` and `θ`.
