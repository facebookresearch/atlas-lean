# Reduced mass matrix of the two-link pendulum

For real `m₁`, `m₂`, `l₁`, `l₂`, `q₁` and `q₂`, the reduced mass matrix in the absolute angles is

`M(q) = [[(m₁ + m₂) l₁², m₂ l₁ l₂ cos (q₁ - q₂)], [m₂ l₁ l₂ cos (q₁ - q₂), m₂ l₂²]]`,

the matrix with `T = wᵀ M(q) w / 2` for the [kinetic energy](kinetic-energy-eq-mass-matrix.md) `T`
at angular velocities `w`. In the model the masses and lengths are positive; the definition takes
any real values.
