# Maximum-likelihood estimator

Let `σ` be a finite set, `law` a map from a set `Θ` to the functions `σ → ℝ`, and `freq n ω : σ → ℝ`
frequency estimates for `n ∈ ℕ` and `ω ∈ Ω`. Estimates `est n ω ∈ Θ` form a maximum-likelihood
estimator for `law` and `freq` if, for every `n` and `ω`, `est n ω` maximizes the
[log-likelihood criterion](log-lik.md) `θ ↦ L(freq n ω, θ) = ∑_a freq n ω a · log (law θ a)` over
all of `Θ`, with the conventions `log 0 = 0` and `log x = log |x|` for `x < 0`. The definition is
algebraic and applies to all real `law` and `freq`. With the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
of a sample as `freq` and a model whose laws are probability vectors positive at the observed
patterns, it maximizes the product of the one-column likelihoods, which is the likelihood of the
sample under the product model, in which the columns are independent with common law `law θ`. In
general it maximizes only this total-log score, which can prefer a model that gives an observed
pattern probability `0`.
