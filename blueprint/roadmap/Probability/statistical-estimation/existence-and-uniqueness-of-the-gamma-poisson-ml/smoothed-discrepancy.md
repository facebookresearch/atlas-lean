# Levin and Reeds's integrated discrepancy

For a finite family of counts `k₁, …, kₙ` with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M`, Levin and
Reeds's integrated discrepancy is the function of a real `u`
`H(u) = ∑ᵢ R_{kᵢ}(u) - n (u² / 2 - (max (u - M) 0)² / 2)`, where `R_k` is the
[ramp sum](ramp-sum.md).

For `u ≥ 0` it is `H(u) = ∫₀ᵘ (G - F)`, where `G(v) = ∑ᵢ G_{kᵢ}(v)` is the number of the unit masses
at `0, 1, …, kᵢ - 1` (over all `i`) that are at most `v`, and `F(v) = n min (v, M)` is the
distribution function of `n` times Lebesgue measure on `[0, M]`. For `u < 0` it is
`H(u) = -n u² / 2`, not that integral (which is `0` there). For an empty family, `M = 0` by the
convention `x / 0 = 0`, and `H = 0`.

For a nonempty family and `a > 0`, the
[profile shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/profile-shape-score.md) is
the transform `H(T) / (a + T)² + 2 ∫₀ᵀ H(u) / (a + u)³ du` of `H`, for every `T` at least `M` and
every count
([the profile shape score as a transform of the integrated discrepancy](profile-shape-score-eq-integral.md)).
