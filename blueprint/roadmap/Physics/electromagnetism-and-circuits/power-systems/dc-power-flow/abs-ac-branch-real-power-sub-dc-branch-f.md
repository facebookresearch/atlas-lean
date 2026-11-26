# Per-branch cubic error of the DC flow for positive susceptances

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed). Suppose that
every branch susceptance is positive, `b_e > 0` for all branches `e`. Then for all real node phase
angles `θ_v` and every branch `e`, the [sending-end real power](ac-branch-real-power.md)
`P_e = b_e sin(θ_{t(e)} - θ_{h(e)})` of the lossless unit-magnitude AC model and the
[DC branch flow](dc-branch-flow.md) `f_e = b_e (θ_{t(e)} - θ_{h(e)})` satisfy

`|P_e - f_e| ≤ b_e |θ_{t(e)} - θ_{h(e)}|³ / 6`.

The bound holds for all angles, with no small-angle assumption; it is `b_e` times the bound
`|x - sin x| ≤ |x|³ / 6`.
