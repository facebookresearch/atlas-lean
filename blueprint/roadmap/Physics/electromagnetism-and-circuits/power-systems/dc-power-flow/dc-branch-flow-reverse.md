# Reversing all branches negates the DC flows

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e` and real node phase angles `θ_v`. If the orientation of every branch is
reversed, tail and head exchanged, the [DC branch flow](dc-branch-flow.md) of each branch `e`
becomes `b_e (θ_{h(e)} - θ_{t(e)}) = -f_e`.
