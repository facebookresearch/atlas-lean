# Axisymmetric Precession euler solve

The witness tests the Euler port of the torque-balance section: for positive inertias,
`I = diag(I_⊥, I_⊥, I₃)` is positive definite, and the angular acceleration that
`euler_solve_iff` determines without torque, `I⁻¹ (0 - ω_B × (I ω_B))`, is the witness's own
`ω_B'`.
