# Delta-v cost of staged burns from their stage masses

Let `n ∈ ℕ`, and for each burn `i ≤ n` let `tb_i ≥ 0`, let `m_i` and `v_i` have derivatives `m_i'`
and `v_i'` at every `t ∈ [0, tb_i]`, with `m_i > 0` on `[0, tb_i]` and the reduced variable-mass law
`m_i(t) v_i'(t) = −ve_i m_i'(t)` there, at an exhaust speed `ve_i > 0`, with burned (not gained)
mass `m_i(tb_i) ≤ m_i(0)`; let the jettisons between burns only drop mass, `m_{i+1}(0) ≤ m_i(tb_i)`
for `i < n`; and let `u_i` be unit vectors of a real normed space `E`, `‖u_i‖ = 1`. Then the start
masses `m_i(0)` and end masses `m_i(tb_i)` are [admissible stage masses](admissible-stage-masses.md)
for the `n + 1` burns, and the [delta-v cost](burn-cost.md) of the burn vectors
`(v_i(tb_i) − v_i(0)) u_i` is `∑_{i=0}^{n} ve_i log(m_i(0) / m_i(tb_i))`, the sum of the
[stage increments](stage-increment.md).
