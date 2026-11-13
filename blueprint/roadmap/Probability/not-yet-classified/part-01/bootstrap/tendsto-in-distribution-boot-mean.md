# Conditional Lindeberg CLT for the bootstrap mean (Bickel–Freedman)

Fix a data sequence `x`. Suppose the plug-in sample variances `empiricalVar x n` converge to
`σ² ≥ 0`, and the centred data satisfy the Lindeberg condition
`(1 / n) ∑_{i<n} (x i - x̄ₙ)² 𝟙{|x i - x̄ₙ| > ε √n} → 0` for every `ε > 0`. Then, under the
bootstrap world (i.e. conditionally on the data), `√n (x̄*ₙ - x̄ₙ)` converges in distribution to
`N(0, σ²)`; for `σ² = 0` this is the point mass at `0`, obtained from Chebyshev's inequality
(the Lindeberg hypothesis is then not used).

For `σ² > 0` the proof applies the triangular-array Lindeberg–Feller theorem
`lindeberg_feller_clt_triangular` to the bootstrap array `(ω n k - x̄ₙ) / √n`, `k < n`, whose
rows are iid from the centred empirical distribution. The data Lindeberg hypothesis is exactly
the Lindeberg condition of that array; it does not follow from the variance condition alone,
which is why an iid central limit theorem for the data cannot replace it.
