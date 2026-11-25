# Body coordinates are recovered from inertial coordinates

For every origin `o ∈ ℝ³`, orientation `R ∈ SO(3)` and body coordinates `x_B ∈ ℝ³`,
`Rᵀ ((o + R x_B) - o) = x_B`: the [body coordinates](inertial-to-body.md) of the point with
[inertial coordinates](body-to-inertial.md) `o + R x_B` are `x_B`.
