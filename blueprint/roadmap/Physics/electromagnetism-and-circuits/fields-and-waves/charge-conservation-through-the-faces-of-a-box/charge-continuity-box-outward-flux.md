# Local continuity gives charge continuity for the six box faces

Let `a ≤ b` coordinatewise, let `J : ℝ³ → ℝ³` be continuous on `[a, b]`, and let `J'` assign to each
point a linear map `ℝ³ → ℝ³` such that `J` has derivative `J'(x)` at every point `x` of the open box
`(a_0, b_0) × (a_1, b_1) × (a_2, b_2)`. Let `ρ̇ : ℝ³ → ℝ` be integrable on `[a, b]` with the local
continuity law `ρ̇(x) + div J'(x) = 0` at every `x ∈ [a, b]`, for the
[divergence](fderiv-divergence.md) `div J'(x) = ∑_i (J'(x) e_i)_i`. Then the
[outward fluxes](box-outward-flux.md) `Φ_0, …, Φ_5` of `J` through the six faces of `[a, b]` satisfy
the [charge-continuity condition](charge-continuity.md) with rate `∫_{[a, b]} ρ̇(x) dx`:

`Φ_0 + ⋯ + Φ_5 = -∫_{[a, b]} ρ̇(x) dx`.
