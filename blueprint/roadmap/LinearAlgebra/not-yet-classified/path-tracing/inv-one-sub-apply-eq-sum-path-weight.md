# Path tracing

**Path tracing** (Wright's rule for recursive linear systems): for a strictly lower
triangular coefficient matrix `B` (a recursive linear structural equation model
`X = B X + ε` on a finite DAG ordered by `Fin n`), the `(i, j)` entry of `(1 - B)⁻¹` is the
sum, over the directed paths from `j` to `i`, of the products of the edge coefficients.
