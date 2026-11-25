# Acceleration of a point in a rotating and translating frame

Let `M` be a rigid-body motion in three dimensions with orientation `t ↦ R(t) ∈ SO(3)` and body
angular velocity `ω_B`, the vector dual to `Rᵀ Ṙ`. Let `o, x_B : ℝ → ℝ³` be an origin and body
coordinates, and `U` an open set of times on which `R` (entry by entry), `o` and `x_B` are `C²`.
At every `t ∈ U`, the point `x = o + R x_B` (its [inertial coordinates](../body-fixed-and-inertial-frames/body-to-inertial.md))
has acceleration `x'' = o'' + R (x_B'' + 2 ω_B × x_B' + ω_B' × x_B + ω_B × (ω_B × x_B))`: the
relative, Coriolis, Euler and centripetal terms.
