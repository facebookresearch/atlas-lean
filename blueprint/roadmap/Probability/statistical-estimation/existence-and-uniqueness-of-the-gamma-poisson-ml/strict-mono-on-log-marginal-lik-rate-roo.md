# The likelihood increases along b = σ a / M when 0 < M and V ≤ M

Let `k₁, …, kₙ` (`n ≥ 1`) be counts with
[sample mean](../likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V`,
observed at a common size factor `σ > 0`, and let `ℓ(a, b)` be their
[log marginal likelihood](../likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. If `M > 0` and `V ≤ M`, then `a ↦ ℓ(a, σ a / M)` is strictly
increasing on `(0, ∞)`. So `ℓ` has no maximizer along this path, and since `b = σ a / M` maximizes
`ℓ(a, ·)` at each shape, none on `(0, ∞)²` either
([no joint MLE](not-exists-is-max-on-log-marginal-lik.md)).
