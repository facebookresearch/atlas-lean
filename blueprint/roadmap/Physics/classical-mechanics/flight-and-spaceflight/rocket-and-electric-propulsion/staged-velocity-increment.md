# Velocity gained over staged burns with jettisons

Let `n ∈ ℕ`, and for each burn `i ≤ n` let `tb_i ≥ 0`, let `m_i` and `v_i` have derivatives `m_i'`
and `v_i'` at every `t ∈ [0, tb_i]`, with `m_i > 0` on `[0, tb_i]` and the reduced law
`m_i(t) v_i'(t) = −ve_i m_i'(t)` there, for reals `ve_i`. Between burn `i` and burn `i + 1`
(`i < n`) assume a jettison, `m_{i+1}(0) ≤ m_i(tb_i)`, that conserves momentum with zero relative
velocity: `m_{i+1}(0) v_{i+1}(0) + (m_i(tb_i) − m_{i+1}(0)) v_i(tb_i) = m_i(tb_i) v_i(tb_i)`. Then
`v_n(tb_n) − v_0(0) = ∑_{i=0}^{n} ve_i log(m_i(0) / m_i(tb_i))`: the velocity gained is the sum of
the burn increments, and no jettisoned mass enters a logarithm. Neither the mass drop nor the sign
of the exhaust speeds is used; in the model `ve_i > 0`.
