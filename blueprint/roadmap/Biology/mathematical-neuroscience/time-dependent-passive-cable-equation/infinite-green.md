# Green's function of the infinite cable

For real numbers `τ`, `ℓ`, `x₀`, `t` and `x`, the Green's function of the infinite cable is

`G(t, x; x₀) = e^(-t/τ) / √(4 π D t) · exp (-(x - x₀)² / (4 D t))`, with `D = ℓ² / τ`.

For `τ > 0`, `ℓ ≠ 0` and `t > 0` it is the potential at position `x ∈ ℝ` and time `t` after a unit
charge is injected at `x₀` at time `0`: a heat kernel with diffusion coefficient `D`, damped by the
membrane leak `e^(-t/τ)`. The formula is defined for all real inputs, with the conventions
`u / 0 = 0` and `√u = 0` for `u < 0`: whenever `4 π D t ≤ 0` the prefactor is `0` and `G = 0`; in
particular `G = 0` for `t ≤ 0` when `τ > 0`, and for every `t` when `ℓ = 0` or `τ = 0`.
