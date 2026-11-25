# Observed versus liability R² of a jointly Gaussian score

Let `μ` be a probability measure on `Ω` and let `S` and `L` be real functions on `Ω` such that the
pair `(S, L)` has a Gaussian law under `μ` (it is `μ`-almost everywhere measurable and its law is a
Gaussian measure on `ℝ²`, possibly degenerate), with `L` measurable and standard normal under `μ`.
Then for every real threshold `t`, with the [case indicator](case-ind.md) `Y = 1{L ≥ t}`, the
[squared correlations](corr-sq.md) satisfy

`corr²(S, Y) = corr²(S, L) · z² / (K (1 - K))`,

with the [prevalence](prevalence.md) `K = K(t)` and the
[standard normal density at the threshold](threshold-density.md) `z = z(t)`. Both sides are `0` when
`Var S = 0`, by the convention `x / 0 = 0`. This is the population-sample form, with case fraction
equal to the prevalence, of the `R²` conversion of Lee, Goddard, Wray and Visscher (2012).
