# Strong consistency of the empirical-Bayes hyperparameters

Let `μ` be a probability measure, `a > 0`, `b > 0`, `s > 0`, and `X₀, X₁, …` real random variables
(e.g. counts) that are pairwise independent and identically distributed, with `X₀` almost-everywhere
strongly measurable, `X₀²` integrable, `E X₀ = m` and `E X₀² = m + m² / a + m²` for `m = s a / b`:
the mean and second moment of the [marginal law](marginal-lik-eq-neg-binomial-real.md)
`NB(a, s a / b)`. Then almost surely, for the [sample mean](sample-mean.md) `M̂ₙ` and the
[sample variance](sample-var.md) `V̂ₙ` of the first `n` observations, the
[shape estimate](mom-shape.md) `â(M̂ₙ, V̂ₙ)` tends to `a`, the [rate estimate](mom-rate.md)
`b̂(s, M̂ₙ, V̂ₙ)` tends to `b`, and for every count `k` the
[empirical-Bayes posterior mean](eb-posterior-mean.md) tends to the oracle posterior mean
`(a + k) / (b + s)`.

The count model enters only through the two moment hypotheses, which hold for a random variable with
the marginal law `NB(a, s a / b)`.

## Sources

- H. Robbins, *An empirical Bayes approach to statistics*, Proc. Third Berkeley Symp. Math. Statist.
  Prob. 1 (1956), 157–163.
- C. N. Morris, *Parametric empirical Bayes inference: theory and applications*, J. Amer. Statist.
  Assoc. 78 (1983), 47–55.
