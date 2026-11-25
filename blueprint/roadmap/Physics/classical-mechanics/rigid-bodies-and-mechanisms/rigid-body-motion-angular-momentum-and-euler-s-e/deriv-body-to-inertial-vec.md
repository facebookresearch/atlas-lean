# Transport law for a vector given in body components

Let `M` be a rigid-body motion in three dimensions with orientation `t ↦ R(t) ∈ SO(3)`, and let
`ω_B(t)` be its body angular velocity, the vector dual to the skew matrix `R(t)ᵀ Ṙ(t)`. For body
components `u : ℝ → ℝ³` and a time `t` at which `R` (entry by entry) and `u` are differentiable,
the [inertial components](../body-fixed-and-inertial-frames/body-to-inertial-vec.md) `R u` satisfy
`d(R u)/dt (t) = R(t) (u'(t) + ω_B(t) × u(t))`.
