# IS-LM solution (MA06.T02)

Under the slope-sign restrictions `0 < b`, `0 < h`,
`0 < k`, the nonsingular system has the explicit solution
`Y = (h * A + b * M) / (h + b * k)` and `r = (k * A - M) / (h + b * k)`.
This is the explicit 2x2 Cramer-rule solution, proved by elimination on the two scalar
equations. It develops no general matrix-inversion theory, and it neither uses nor
reproves `Matrix.mul_nonsing_inv` (which states `A * A⁻¹ = 1`, not the solution formula);
the scalar solution is the usable form.
