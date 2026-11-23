# Strong consistency of the empirical-Bayes hyperparameters

Let `X₀, X₁, …` be pairwise
independent, identically distributed real random variables (e.g. counts) with finite second
moment (`X₀` a.e.-strongly measurable with `X₀²` integrable, which gives `X₀` integrable on the
probability space) whose mean and second moment are those of the hierarchy's marginal law
`NB(a, s a / b)`: `E X₀ = s a / b` and `E X₀² = μ + μ² / a + μ²` with `μ = s a / b`. Then almost
surely the moment estimates computed from the first `n` observations converge to `(a, b)`, and
for every count `k` the empirical-Bayes posterior mean converges to the oracle posterior mean
`(a + k) / (b + s)`.

The moment hypotheses are where the count model enters: they are exactly the pmf-level facts
`ProbabilityTheory.hasSum_mul_negBinomialReal` and `ProbabilityTheory.hasSum_sq_negBinomialReal`
for `marginalLik a b s = NB(a, s a / b)` (`marginalLik_eq_negBinomialReal`), transported to a
random variable whose law is that pmf.
