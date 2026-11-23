# Liability-scale R² of a jointly Gaussian score from its observed R²

Let `μ` be a probability measure on `Ω` and let `S` and `L` be real functions on `Ω` such that the
pair `(S, L)` has a Gaussian law under `μ` (it is `μ`-almost everywhere measurable and its law is a
Gaussian measure on `ℝ²`, possibly degenerate), with `L` measurable and standard normal under `μ`.
Then for every real threshold `t`, with the [case indicator](case-ind.md) `Y = 1{L ≥ t}`, the
[squared correlations](corr-sq.md) satisfy

`corr²(S, L) = corr²(S, Y) · K (1 - K) / z²`,

the observed-scale value times the [population conversion factor](pop-liability-factor.md), with the
[prevalence](prevalence.md) `K = K(t)` and the
[standard normal density at the threshold](threshold-density.md) `z = z(t)`.
