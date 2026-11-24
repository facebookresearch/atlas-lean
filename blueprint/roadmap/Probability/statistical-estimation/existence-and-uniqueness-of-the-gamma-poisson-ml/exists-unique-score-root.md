# Exactly one joint score root at a common size factor when 0 < M < V

Let `k₁, …, kₙ` (`n ≥ 1`) be counts with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V`,
observed at a common size factor `σ > 0`, and let `ℓ(a, b)` be their
[log marginal likelihood](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. If `0 < M < V`, exactly one `(a, b)` with `a > 0` and `b > 0`
solves the joint score equations, that is, the
[shape score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/shape-score.md) `∂ℓ/∂a` and the
[rate score](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/rate-score.md) `∂ℓ/∂b` both vanish
at `(a, b)`. This answers Anscombe's (1950) question on the uniqueness of the negative binomial
maximum likelihood estimate (Levin and Reeds 1977, Theorem 2).
