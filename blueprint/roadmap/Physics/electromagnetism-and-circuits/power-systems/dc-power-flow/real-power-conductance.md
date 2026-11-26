# Sending-end real power of a conductance branch at unit magnitudes

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch conductances `g_e`, used as the branch admittances, and real node phase angles `θ_v`. Take
the unit-magnitude voltages `V_v = exp(i θ_v)` and the branch currents
`I_e = g_e (V_{t(e)} - V_{h(e)})`. Then for every branch `e`,

`Re(V_{t(e)} conj(I_e)) = g_e (1 - cos(θ_{t(e)} - θ_{h(e)}))`,

for all real `g` and `θ`. This term is even in the angle difference, whereas the DC flow
`b_e (θ_{t(e)} - θ_{h(e)})` is odd; the lossless DC model has no such term. In the physical reading
the conductances are nonnegative.
