# At most one joint score root at a common size factor when 0 < M < V

Let `k₁, …, kₙ` (`n ≥ 1`) be counts with
[sample mean](../likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V`,
observed at a common size factor `σ > 0`, and let `ℓ(a, b)` be their
[log marginal likelihood](../likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. Assume `0 < M < V`. If `(a, b)` and `(a', b')` in `(0, ∞)²` both
solve the joint score equations, that is, at each of them the
[shape score](../likelihood-equations-and-efficiency-of-the-gamma/shape-score.md) `∂ℓ/∂a` and the
[rate score](../likelihood-equations-and-efficiency-of-the-gamma/rate-score.md) `∂ℓ/∂b` both vanish,
then `a = a'` and `b = b'`.
