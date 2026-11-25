# Sine formula for the lossless sending-end real power

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed). For all real
branch susceptances `b_e` and node phase angles `θ_v`, the
[sending-end real power](ac-branch-real-power.md) of branch `e` in the lossless unit-magnitude AC
model is

`P_e = Re(V_{t(e)} conj(I_e)) = b_e sin(θ_{t(e)} - θ_{h(e)})`,

with `V_v = exp(i θ_v)` and `I_e = -i b_e (V_{t(e)} - V_{h(e)})`. In the physical reading the
susceptances are positive; the identity holds for all real `b`.
