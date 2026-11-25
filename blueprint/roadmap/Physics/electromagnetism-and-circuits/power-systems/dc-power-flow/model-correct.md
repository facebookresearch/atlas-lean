# Lossless DC flow model and its cubic error for positive susceptances

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed). Suppose that
`b_e > 0` for every branch `e`. Then for all real node phase angles `θ_v`:

- the [DC branch flow](dc-branch-flow.md) is `f_e = b_e (θ_{t(e)} - θ_{h(e)})` for every
  branch `e`;
- the [DC nodal injection](dc-injection.md) is `p = L_b θ`, with `L_b` the full
  [susceptance-weighted Laplacian](weighted-laplacian.md);
- the [sending-end real power](ac-branch-real-power.md) of the lossless unit-magnitude AC model
  is `P_e = b_e sin(θ_{t(e)} - θ_{h(e)})` for every branch `e`;
- `|P_e - f_e| ≤ b_e |θ_{t(e)} - θ_{h(e)}|³ / 6` for every branch `e`.

Only the last statement uses the positivity of the susceptances; the first three hold for all real
`b`.
