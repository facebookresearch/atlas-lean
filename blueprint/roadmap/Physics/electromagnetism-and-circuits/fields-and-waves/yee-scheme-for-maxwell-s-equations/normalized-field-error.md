# Normalized error of the Yee iterates

For free space with permittivity `ε₀ > 0` and permeability `μ₀ > 0`, `E_y, H_z : ℝ² → ℝ`, `h`, `dt`,
initial grid fields `E0, H0 ∈ ℝᴺ` and a step `n`: the pair norm of
`(√ε₀ (U_n − Eⁿ), −√μ₀ (V_n − Hⁿ))`, where `(Eⁿ, Hⁿ)` is the `n`-th
[physical Yee iterate](physical-yee-iterate.md) from `(E0, H0)`, with the staggered samples
`U_n = (E_y(n dt, j h))_j` and `V_n = (H_z(n dt − dt/2, j h − h/2))_j`, `j = 0, …, N − 1`, and the
pair norm `‖(p, q)‖ = √(h ∑_j p_j² + h ∑_j q_j²)` (`0` when the radicand is negative, as for
`h < 0`).
