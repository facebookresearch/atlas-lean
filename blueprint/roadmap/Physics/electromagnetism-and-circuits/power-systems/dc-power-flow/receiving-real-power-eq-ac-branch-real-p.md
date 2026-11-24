# On a lossless branch, receiving-end equals sending-end real power

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e` and real node phase angles `θ_v`. Take the unit-magnitude voltages
`V_v = exp(i θ_v)` and the lossless branch currents `I_e = -i b_e (V_{t(e)} - V_{h(e)})`. For every
branch `e`, the real power at the receiving end equals the
[sending-end real power](ac-branch-real-power.md):

`Re(V_{h(e)} conj(I_e)) = Re(V_{t(e)} conj(I_e)) = b_e sin(θ_{t(e)} - θ_{h(e)})`,

so the branch loses no real power. The identity holds for all real `b` and `θ`.
