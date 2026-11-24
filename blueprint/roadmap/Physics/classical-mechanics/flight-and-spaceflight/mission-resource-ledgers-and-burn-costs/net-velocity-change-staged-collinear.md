# For collinear staged burns the net change has the norm of the cost

Let `n ∈ ℕ`, and for each burn `i ≤ n` let `tb_i ≥ 0`, let `m_i` and `v_i` have derivatives `m_i'`
and `v_i'` at every `t ∈ [0, tb_i]`, with `m_i > 0` on `[0, tb_i]` and the reduced variable-mass law
`m_i(t) v_i'(t) = −ve_i m_i'(t)` there, at an exhaust speed `ve_i > 0`, with burned (not gained)
mass `m_i(tb_i) ≤ m_i(0)`; let the jettisons between burns only drop mass, `m_{i+1}(0) ≤ m_i(tb_i)`
for `i < n`; let the jettisons conserve momentum with zero relative velocity,
`m_{i+1}(0) v_{i+1}(0) + (m_i(tb_i) − m_{i+1}(0)) v_i(tb_i) = m_i(tb_i) v_i(tb_i)` for `i < n`; and
let `u` be one unit vector of a real normed space `E`, `‖u‖ = 1`. Then the
[net velocity change](net-velocity-change.md) of the burn vectors `(v_i(tb_i) − v_i(0)) u` is
`(v_n(tb_n) − v_0(0)) u`, the staged velocity gain along `u`, and its norm equals their
[delta-v cost](burn-cost.md).
