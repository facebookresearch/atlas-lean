# Lossless AC nodal real power is a signed sum of branch sine flows

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed). For all real
branch susceptances `b_e` and node phase angles `θ_v`, let `S_v` be the
[complex power supplied by node](../ac-power-injections-and-network-losses/node-complex-power.md)
`v` for the
[electrical incidence](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md)
`B`, the unit-magnitude voltages `exp(i θ_u)`, the lossless branch admittances `-i b_e` and no
shunts. Then

`Re S_v = ∑_e B_{ve} b_e sin(θ_{t(e)} - θ_{h(e)})`,

the nonlinear counterpart of the [DC injection](dc-injection.md) `p_v = ∑_e B_{ve} f_e`.
