# Covariance of a jointly Gaussian score with the case indicator

Let `μ` be a probability measure on `Ω` and let `S` and `L` be real functions on `Ω` such that the
pair `(S, L)` has a Gaussian law under `μ` (it is `μ`-almost everywhere measurable and its law is a
Gaussian measure on `ℝ²`, possibly degenerate), with `L` measurable and standard normal under `μ`.
Then for every real threshold `t`, with the [case indicator](case-ind.md) `Y = 1{L ≥ t}`,

`Cov(S, Y) = Cov(S, L) · z(t)`,

with the [standard normal density at the threshold](threshold-density.md) `z = z(t)`.
