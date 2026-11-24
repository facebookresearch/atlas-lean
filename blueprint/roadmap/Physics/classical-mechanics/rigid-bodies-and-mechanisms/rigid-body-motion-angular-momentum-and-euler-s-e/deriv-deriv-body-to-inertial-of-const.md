# Acceleration in a frame with constant rotation rate and fixed origin

Let `M` be a rigid-body motion in three dimensions with orientation `t ↦ R(t) ∈ SO(3)` and body
angular velocity `ω_B`, let `o₀ ∈ ℝ³` be a fixed origin, `x_B : ℝ → ℝ³` body coordinates, `Ω ∈ ℝ³`,
and `U` an open set of times on which `R` (entry by entry) and `x_B` are `C²` and `ω_B = Ω`. At
every `t ∈ U`, the point `o₀ + R x_B` has acceleration `R (a + 2 Ω × v + Ω × (Ω × r))`, with
`r = x_B`, `v = x_B'` and `a = x_B''`: the right side of the
[constant-rate decomposition](../rotating-frames-and-the-coriolis-force/rotating-acceleration-decomposition.md),
here derived from the motion.
