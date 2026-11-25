# The fixed-margin statistic as a normalized contrast

For `R ≤ N`, genotype classes `g_k ∈ {0, 1, 2}`, a real number `μ` and a real number `v > 0`, with
the genotype scores `x_k = g_k`, the [contrast weights](fm-weight.md) `w_k` and the convention
`x / 0 = 0`, the [fixed-margin statistic](fm-stat.md) is

`T(R, N, g) = (U / B)² / ((N ∑_{k<N} x_k² − (∑_{k<N} x_k)²) / (N² v))`,

where `U = ∑_{k<N} w_k (x_k − μ)` and `B = √(R (N − R) N v)`. Since the weights `w_k`, `k < N`, sum
to `0`, `U` does not depend on `μ`; in the asymptotic theorem `μ` and `v` are the mean and the
variance of the score. For `R = 0`, for `R = N` and when all scores `x_k`, `k < N`, are equal, both
sides are `0`.
