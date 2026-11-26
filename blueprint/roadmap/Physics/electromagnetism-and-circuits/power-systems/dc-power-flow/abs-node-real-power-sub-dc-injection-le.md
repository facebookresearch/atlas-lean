# Nodal cubic error of the DC injection for positive susceptances

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed). Suppose that
`b_e > 0` for every branch `e`. For real node phase angles `θ_u`, let `S_v` be the
[complex power supplied by node](../ac-power-injections-and-network-losses/node-complex-power.md)
`v` for the
[electrical incidence](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)
`B`, the unit-magnitude voltages `exp(i θ_u)`, the lossless branch admittances `-i b_e` and no
shunts. Then for all such angles and every node `v`, the [DC nodal injection](dc-injection.md) `p_v`
satisfies

`|Re S_v - p_v| ≤ ∑_e |B_{ve}| b_e |θ_{t(e)} - θ_{h(e)}|³ / 6`,

where `|B_{ve}| = 1` for the branches incident to `v` that are not loops and `0` otherwise: the sum
of the [per-branch bounds](abs-ac-branch-real-power-sub-dc-branch-f.md) over these branches.
