# Under overdispersion the profile shape score crosses zero at most once

Let `k₁, …, kₙ` (`n ≥ 1`) be counts with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V` such
that `M < V` (which forces `M > 0`). If the
[profile shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/profile-shape-score.md)
`P(a) = ∑ᵢ ∑_{j<kᵢ} 1 / (a + j) - n (log (a + M) - log a)` satisfies `P(a) ≤ 0` at some `a > 0`,
then `P(a') < 0` for every `a' > a`. This is the "at most one root" part of Levin and Reeds (1977),
Theorem 2, for the likelihood equation in the shape.

The proof writes `P(a) = H(T) / (a + T)² + 2 ∫₀ᵀ H(u) / (a + u)³ du` for a `T` beyond every count
([the profile shape score as a transform of the integrated discrepancy](profile-shape-score-eq-integral.md)),
where `H` is Levin and Reeds's [integrated discrepancy](smoothed-discrepancy.md). On `[0, ∞)`, `H`
is nonnegative before a point `u*` and negative after it
([once negative, it stays negative](smoothed-discrepancy-neg-of-le.md)), and
`H(T) = n (M - V) / 2 < 0`. The kernel `((a + u*) / (a + u))³` decreases in `a` for `u ≤ u*` and
increases in `a` for `u ≥ u*`, and `(a + u*)³ / (a + T)²` increases strictly in `a`, so
`a ↦ (a + u*)³ P(a)` is strictly decreasing.
