# Sample Cov expectation

Assume `∀ i j, ∫ ω, X i ω j ∂μ = m j` and `∀ i j k, cov[fun ω => X i ω j, fun ω => X i ω k; μ] = Sig j k`.

Unbiasedness, entrywise: for `N ≥ 2` square-integrable sample vectors in `Fin d → ℝ` that
are pairwise independent and share the mean `m` and the coordinate covariance matrix `Σ`, the
expectation of the sample covariance is `Σ`. The samples need not be identically distributed or
mutually independent.
