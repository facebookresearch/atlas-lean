# No joint MLE at a common size factor when V ≤ M

Let `k₁, …, kₙ` (`n ≥ 1`) be counts with
[sample mean](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-mean.md) `M` and
[biased sample variance](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/count-var.md) `V`,
observed at a common size factor `σ > 0`, and let `ℓ(a, b)` be their
[log marginal likelihood](../../../Probability/statistical-estimation/likelihood-equations-and-efficiency-of-the-gamma/log-marginal-lik.md)
in the shape `a` and the rate `b`. If `M > 0` and `V ≤ M`, then `ℓ` has no maximizer on `(0, ∞)²`:
no `(â, b̂)` with `â > 0` and `b̂ > 0` satisfies `ℓ(a, b) ≤ ℓ(â, b̂)` for all `a > 0` and `b > 0`.
Indeed every `(a, b) ∈ (0, ∞)²` has `ℓ(a, b) < ℓ(a + 1, σ (a + 1) / M)`.

This is the converse half of Levin and Reeds (1977), Theorem 2, for samples with `M > 0`: the
maximum occurs at a finite shape only if `M < V`.
