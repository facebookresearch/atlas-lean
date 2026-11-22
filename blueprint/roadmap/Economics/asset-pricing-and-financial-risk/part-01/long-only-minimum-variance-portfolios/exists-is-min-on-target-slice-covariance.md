# Exists is Min On target Slice covariance

Covariance form: for square-integrable returns `R` with expectations
`μv i = ∫ ω, R i ω ∂μ`, a nonempty long-only target slice attains the
minimum of the covariance quadratic form. The matrix is spelled with
Mathlib `covariance`, entrywise the native `covMatrix`.
