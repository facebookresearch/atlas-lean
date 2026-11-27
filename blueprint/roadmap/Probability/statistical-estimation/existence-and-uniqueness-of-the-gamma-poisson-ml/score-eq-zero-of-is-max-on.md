# Every joint MLE at a common size factor solves the score equations

Let `k₁, …, kₙ` (`n ≥ 1`) be counts with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V`,
observed at a common size factor `σ > 0`, and let `ℓ(a, b)` be their
[log marginal likelihood](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. Assume `0 < M < V`. If `(a, b)` with `a > 0` and `b > 0`
maximizes `ℓ` over `(0, ∞)²`, that is, `ℓ(a', b') ≤ ℓ(a, b)` for all `a' > 0` and `b' > 0`, then
`(a, b)` solves the joint score equations: the
[shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/shape-score.md) `∂ℓ/∂a` and the
[rate score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/rate-score.md) `∂ℓ/∂b` both vanish
at `(a, b)`.
