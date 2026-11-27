# Exactly one joint MLE at a common size factor when 0 < M < V

Let `k₁, …, kₙ` (`n ≥ 1`) be counts with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V`,
observed at a common size factor `σ > 0`, and let `ℓ(a, b)` be their
[log marginal likelihood](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. If `0 < M < V`, then `ℓ` has exactly one maximizer over
`(0, ∞)²`: there is exactly one `(â, b̂)` with `â > 0`, `b̂ > 0` and `ℓ(a, b) ≤ ℓ(â, b̂)` for every
`a > 0` and `b > 0` (Levin and Reeds 1977, Theorem 2; Anscombe 1950).

This maximizer solves the joint score equations
([every joint MLE solves them](score-eq-zero-of-is-max-on.md)), so it is their only root in
`(0, ∞)²` ([exactly one joint score root](exists-unique-score-root.md)), and its rate is
`b̂ = σ â / M`
([joint score equations at a common size factor](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/score-eq-zero-iff-const.md)).
