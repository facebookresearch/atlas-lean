# Maximum-likelihood estimator

Let `σ` be a finite set, `law` a map from a set `Θ` to the functions `σ → ℝ`, and `freq n ω : σ → ℝ`
frequency estimates for `n ∈ ℕ` and `ω ∈ Ω`. Estimates `est n ω ∈ Θ` form a maximum-likelihood
estimator for `law` and `freq` if, for every `n` and `ω`, `est n ω` maximizes the
[log-likelihood criterion](log-lik.md) `θ ↦ L(freq n ω, θ)` over all of `Θ`. With the
[empirical site-pattern frequencies](../consistency-of-minimum-distance-gtr-estimators/empirical-freq.md)
of a sample as `freq`, this is a maximum-likelihood estimator from the sample.
