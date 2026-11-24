# Inertial coordinates are recovered from body coordinates

For every origin `o ∈ ℝ³`, orientation `R ∈ SO(3)` and inertial coordinates `x_I ∈ ℝ³`,
`o + R Rᵀ (x_I - o) = x_I`: the [inertial coordinates](body-to-inertial.md) of the point with
[body coordinates](inertial-to-body.md) `Rᵀ (x_I - o)` are `x_I`.
