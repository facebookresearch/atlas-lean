# With local continuity, box terminal currents sum to minus ∫ρ̇

Let `a ≤ b` coordinatewise, let `J : ℝ³ → ℝ³` be continuous on `[a, b]`, and let `J'` assign to each
point a linear map `ℝ³ → ℝ³` such that `J` has derivative `J'(x)` at every point `x` of the open box
`(a_0, b_0) × (a_1, b_1) × (a_2, b_2)`. Let `ρ̇ : ℝ³ → ℝ` be integrable on `[a, b]` with
`ρ̇(x) + div J'(x) = 0` at every `x ∈ [a, b]`, for the [divergence](fderiv-divergence.md)
`div J'(x) = ∑_i (J'(x) e_i)_i`. If the terminal currents `I_0, …, I_5` are the
[outward fluxes](box-outward-flux.md) of `J` through the six faces, then

`I_0 + ⋯ + I_5 = -∫_{[a, b]} ρ̇(x) dx`.

When `ρ̇ = ρ̇(t, ·)` for a charge density `ρ`, with `ρ` and `ρ̇` jointly continuous in time and
position and `∂ₛρ(s, x) = ρ̇(s, x)` for all `s` and `x`, the right side is minus the rate of change
at time `t` of the enclosed charge ([enclosed-charge derivative](has-deriv-at-enclosed-charge.md)).
