# At a common size factor a score root is the strict global maximizer

Let `k₁, …, kₙ` (`n ≥ 1`) be counts with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V`,
observed at a common size factor `σ > 0`, and let `ℓ(a, b)` be their
[log marginal likelihood](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. Assume `0 < M < V`. If `(â, b̂)` with `â > 0` and `b̂ > 0` solves
the joint score equations (the
[shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/shape-score.md) `∂ℓ/∂a` and the
[rate score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/rate-score.md) `∂ℓ/∂b` both vanish
at `(â, b̂)`), then `ℓ(a, b) < ℓ(â, b̂)` for every `(a, b) ∈ (0, ∞)²` other than `(â, b̂)`.

The proof profiles out the rate: `ℓ(a, b) ≤ ℓ(a, σ a / M)`, with equality only at `b = σ a / M`, and
`ℓ(a, σ a / M)` is the [profile log likelihood](profile-log-lik.md) plus a constant. By
[single crossing](profile-shape-score-neg-of-le.md) its derivative, the
[profile shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/profile-shape-score.md),
is positive on `(0, â)` and negative on `(â, ∞)`.
