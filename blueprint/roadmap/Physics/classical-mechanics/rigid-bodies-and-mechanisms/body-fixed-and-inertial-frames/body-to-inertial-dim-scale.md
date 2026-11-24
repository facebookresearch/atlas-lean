# A change of length unit rescales all point coordinates alike

Let `u₁` and `u₂` be unit choices on the seven ISQ base dimensions (each base unit of positive
magnitude), and `λ = u₁(L) / u₂(L) > 0` the factor by which a length coordinate in `u₁` is
multiplied to give the coordinate in `u₂`. For every origin `o ∈ ℝ³`, orientation `R ∈ SO(3)` and
body coordinates `x_B ∈ ℝ³`, `(λ o) + R (λ x_B) = λ (o + R x_B)`: expressing the origin and the body
coordinates in the new length unit rescales the [inertial coordinates](body-to-inertial.md) by the
same factor.
