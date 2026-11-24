# Sending-end real power of a lossless branch

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e` and real node phase angles `θ_v`. Take the
[unit-magnitude voltages](unit-voltage.md) `V_v = exp(i θ_v)` and the
[branch currents](branch-current.md) `I_e = y_e d_e` of the
[lossless admittances](lossless-admittance.md) `y_e = -i b_e` through the
[electrical incidence](../../../../GraphTheory/algebraic-graph-theory/part-01/oriented-incidence-matrices/oriented-incidence.md),
so that `d_e = V_{t(e)} - V_{h(e)}`. The sending-end real power of branch `e` is

`P_e = Re(V_{t(e)} conj(I_e))`,

the real part of the [complex power](../balanced-three-phase-power/complex-power.md) at the tail. It
[equals `b_e sin(θ_{t(e)} - θ_{h(e)})`](ac-branch-real-power-eq-mul-sin.md). In the physical reading
the susceptances are positive; the definition allows all real `b` and `θ`.
