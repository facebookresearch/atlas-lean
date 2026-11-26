# Under local continuity at time t, the charge rate is minus the outflux

Let `a ≤ b` coordinatewise, let `J : ℝ³ → ℝ³` be continuous on `[a, b]`, and let `J'` assign to each
point a linear map `ℝ³ → ℝ³` such that `J` has derivative `J'(x)` at every point `x` of the open box
`(a_0, b_0) × (a_1, b_1) × (a_2, b_2)`. Let `ρ, ρ̇ : ℝ × ℝ³ → ℝ` be jointly continuous in time and
position, with `s ↦ ρ(s, x)` differentiable at every time `s` with derivative `ρ̇(s, x)`, for every
`x ∈ ℝ³`. Assume that at time `t` the local continuity law `ρ̇(t, x) + div J'(x) = 0` holds at every
`x ∈ [a, b]`, with the [divergence](fderiv-divergence.md) `div J'(x) = ∑_i (J'(x) e_i)_i`. Then the
[enclosed charge](enclosed-charge.md) `Q(s) = ∫_{[a, b]} ρ(s, x) dx` has derivative at `t`

`Q'(t) = -(Φ_0 + ⋯ + Φ_5)`,

where `Φ_0, …, Φ_5` are the [outward fluxes](box-outward-flux.md) of `J` through the six faces of
`[a, b]`.
