# The profile shape score as a transform of the integrated discrepancy

For a nonempty finite family of counts `k₁, …, kₙ` with
[sample mean](../likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M`, every `a > 0`
and every real `T` with `T ≥ M` and `T ≥ kᵢ` for every `i`, the
[profile shape score](../likelihood-equations-and-efficiency-of-the-gamma/profile-shape-score.md)
`∑ᵢ ∑_{j<kᵢ} 1 / (a + j) - n (log (a + M) - log a)` equals
`H(T) / (a + T)² + 2 ∫₀ᵀ H(u) / (a + u)³ du`, where `H` is Levin and Reeds's
[integrated discrepancy](smoothed-discrepancy.md) (Levin and Reeds 1977, §3.1).

The identity adds up the [transform of one ramp](ramp-transform.md) over the unit masses at
`0, 1, …, kᵢ - 1` and subtracts `n` times the transform of the uniform part, which is
`log (a + M) - log a - M / (a + T)`.
