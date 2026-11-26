# Divergence theorem for the six faces of a box

Let `a ≤ b` coordinatewise, let `J : ℝ³ → ℝ³` be continuous on `[a, b]`, and let `J'` assign to each
point a linear map `ℝ³ → ℝ³` such that `J` has derivative `J'(x)` at every point `x` of the open box
`(a_0, b_0) × (a_1, b_1) × (a_2, b_2)`. Assume the [divergence](fderiv-divergence.md)
`div J'(x) = ∑_i (J'(x) e_i)_i` is integrable on `[a, b]`. Then the
[outward fluxes](box-outward-flux.md) `Φ_0, …, Φ_5` of `J` through the six faces of `[a, b]` satisfy

`Φ_0 + Φ_1 + Φ_2 + Φ_3 + Φ_4 + Φ_5 = ∫_{[a, b]} div J'(x) dx`.
