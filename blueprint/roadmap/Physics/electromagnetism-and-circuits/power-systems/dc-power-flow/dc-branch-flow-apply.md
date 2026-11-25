# DC flow is susceptance times the angle difference across the branch

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e` and real node phase angles `θ_v`. For every branch `e`, the
[DC branch flow](dc-branch-flow.md) is

`f_e = b_e (θ_{t(e)} - θ_{h(e)})`.

In the physical reading the susceptances are positive, so the flow runs from the end with the larger
angle to the end with the smaller one; the formula holds for all real `b` and `θ`.
