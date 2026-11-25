# Lossless sending-end real power with non-unit voltage magnitudes

Consider a network with nodes `0, …, n_N - 1` and branches `0, …, n_E - 1`, branch `e` running from
its tail `t(e)` to its head `h(e)` (loops `t(e) = h(e)` and parallel branches allowed), with real
branch susceptances `b_e`, real node phase angles `θ_v` and real magnitudes `m_v`. Take the voltages
`V_v = m_v exp(i θ_v)` and the lossless branch currents `I_e = -i b_e (V_{t(e)} - V_{h(e)})`. Then
for every branch `e`,

`Re(V_{t(e)} conj(I_e)) = b_e m_{t(e)} m_{h(e)} sin(θ_{t(e)} - θ_{h(e)})`,

the unit-magnitude value `b_e sin(θ_{t(e)} - θ_{h(e)})` times `m_{t(e)} m_{h(e)}`, so the
[cubic per-branch bound](abs-ac-branch-real-power-sub-dc-branch-f.md) need not hold when
`m_{t(e)} m_{h(e)} ≠ 1`. In the physical reading the magnitudes and the susceptances are positive;
the identity holds for all real `b`, `m` and `θ`.
