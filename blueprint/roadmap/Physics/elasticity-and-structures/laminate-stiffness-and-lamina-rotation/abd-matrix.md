# Block stiffness matrix of a laminate

For `n ∈ ℕ`, interfaces `z_0, …, z_n` (heights from the reference plane) and ply stiffnesses
`Q̄_0, …, Q̄_{n−1}` (real `3 × 3` matrices in global axes, ply `i` occupying `[z_i, z_{i+1}]`), the
real `6 × 6` block matrix `[[A, B], [B, D]]` built from the [extensional](extensional-stiffness.md),
[coupling](coupling-stiffness.md) and [bending](bending-stiffness.md) stiffnesses, indexed by two
copies of `{0, 1, 2}` and acting on the pair `(ε⁰, κ)` of midplane strain and curvature.
