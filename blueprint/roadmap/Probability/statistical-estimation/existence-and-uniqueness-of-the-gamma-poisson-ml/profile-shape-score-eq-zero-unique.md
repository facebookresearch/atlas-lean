# When M < V the profile shape score has at most one positive root

For counts `k₁, …, kₙ` (`n ≥ 1`) with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V` such
that `M < V`, the
[profile shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/profile-shape-score.md)
`P(a) = ∑ᵢ ∑_{j<kᵢ} 1 / (a + j) - n (log (a + M) - log a)` has at most one root in `(0, ∞)`: if
`a > 0`, `a' > 0` and `P(a) = P(a') = 0`, then `a = a'`.
