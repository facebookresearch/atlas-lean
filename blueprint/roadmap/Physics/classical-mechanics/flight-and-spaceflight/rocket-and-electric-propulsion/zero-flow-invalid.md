# Zero flow leaves the efficiency undefined

For `m_i, q_i, V_b > 0` and no beam current
the beam mass flow is `0`, so the efficiency denominator `2 ṁ P_in` vanishes (Lean's `x / 0 = 0`
then makes `T² / (2 ṁ P_in)` equal `0`, which is not a physical efficiency), while each ion would
still leave at `v_e > 0`.
