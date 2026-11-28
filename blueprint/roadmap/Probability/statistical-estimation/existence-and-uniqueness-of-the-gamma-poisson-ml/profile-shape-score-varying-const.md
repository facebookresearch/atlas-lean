# Closed form of the profile at a common size factor

For counts `k₁, …, kₙ` (`n ≥ 1`) with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M > 0`, a common
size factor `σ > 0` and a shape `a > 0`, the
[profile shape score along the rate root](profile-shape-score-varying.md) equals the
[profile shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/profile-shape-score.md)
`∑ᵢ ∑_{j<kᵢ} 1 / (a + j) - n (log (a + M) - log a)`, which does not depend on `σ`. The condition
`M > 0` matters: with all counts `0`, the rate root is `0`, the left side is `-n log σ` and the
right side is `0`.
