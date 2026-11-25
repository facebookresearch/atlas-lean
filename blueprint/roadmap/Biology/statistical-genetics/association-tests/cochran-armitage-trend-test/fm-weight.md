# Contrast weight of a subject in a fixed-margin design

For `R, N, k ∈ ℕ`, the contrast weight is `w_k = N − R` if `k < R` (a case) and `w_k = −R` otherwise
(a control, and also every `k ≥ N`), as real numbers. For `R ≤ N` the trend numerator of the
[fixed-margin statistic](fm-stat.md) is `U = ∑_{k<N} w_k x_k`, where `x_k` is the genotype score of
subject `k`.
