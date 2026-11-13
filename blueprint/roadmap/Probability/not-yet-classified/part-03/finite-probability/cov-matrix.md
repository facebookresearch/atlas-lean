# Cov Matrix

The covariance matrix of the finite random vector `X : α → n → ℝ` (outcome `x` ↦ vector
`X x`): entry `(i, j)` is the covariance of coordinates `i` and `j` (MF06.2). Mathlib's
`ProbabilityTheory.covarianceBilin` is a bilinear form for measures on a normed space; this is
the matrix of pairwise finite covariances.
