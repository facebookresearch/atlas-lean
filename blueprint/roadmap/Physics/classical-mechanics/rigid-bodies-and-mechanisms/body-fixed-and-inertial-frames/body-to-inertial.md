# Inertial coordinates of a point given in body coordinates

For a point `o ∈ ℝ³`, the inertial coordinates of the origin of a body frame, an orientation
`R ∈ SO(3)` (a real 3 × 3 matrix with `Rᵀ R = 1` and `det R = 1`) and body coordinates `x_B ∈ ℝ³`,
the inertial coordinates of the point are `x_I = o + R x_B`. The columns of `R` are the body axes
written in inertial components.
