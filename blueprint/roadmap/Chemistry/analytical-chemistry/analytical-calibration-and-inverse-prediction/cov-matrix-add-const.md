# A constant shift leaves the covariance matrix unchanged

A constant shift does not change the finite covariance matrix: for weights `p` with
`∑ ω, p ω = 1` and a constant vector `c`, `Cov(c + ε) = Cov(ε)`, where `Cov(ε)` has entries
`E[(ε i - E[ε i]) * (ε j - E[ε j])]` and `E[f] = ∑ ω, p ω * f ω`. So the covariance of
`y = Xβ + ε` is that of `ε`.
