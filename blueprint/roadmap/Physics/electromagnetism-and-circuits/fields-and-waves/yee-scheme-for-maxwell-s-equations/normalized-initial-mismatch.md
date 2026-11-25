# Normalized initial mismatch of the Yee scheme

For free space with permittivity `ε₀ > 0` and permeability `μ₀ > 0`, `E_y, H_z : ℝ² → ℝ`, `h`, `dt`
and initial grid fields `E0, H0 ∈ ℝᴺ`: the pair norm of `(√ε₀ (U_0 − E0), −√μ₀ (V_0 − H0))`, with
`U_0 = (E_y(0, j h))_j` and `V_0 = (H_z(−dt/2, j h − h/2))_j` (the `H` sample at the half time
`−dt/2`), and the pair norm `‖(p, q)‖ = √(h ∑_j p_j² + h ∑_j q_j²)` (`0` when the radicand is
negative, as for `h < 0`).
