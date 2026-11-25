# The profile shape score is positive when 0 < M and V ≤ M

For counts `k₁, …, kₙ` (`n ≥ 1`) with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V` such
that `M > 0` and `V ≤ M`, the
[profile shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/profile-shape-score.md)
`P(a) = ∑ᵢ ∑_{j<kᵢ} 1 / (a + j) - n (log (a + M) - log a)` is positive at every `a > 0` (the
converse half of Levin and Reeds 1977, Theorem 2).

In `P(a) = H(T) / (a + T)² + 2 ∫₀ᵀ H(u) / (a + u)³ du`, with `T` beyond every count and `H` Levin
and Reeds's [integrated discrepancy](smoothed-discrepancy.md)
([the transform](profile-shape-score-eq-integral.md)), `H ≥ 0` on `[0, ∞)`
([when V ≤ M](smoothed-discrepancy-nonneg.md)). As some count is positive, `H(u) ≥ u - n u² / 2 > 0`
for small `u > 0`, so the integral is positive.
