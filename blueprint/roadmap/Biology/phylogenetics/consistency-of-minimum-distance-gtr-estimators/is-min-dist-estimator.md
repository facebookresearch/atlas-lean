# Minimum-distance estimator

Let `σ` be a finite set, `law` a map from a set `Θ` of parameters to the functions `σ → ℝ`, and
`freq n ω : σ → ℝ` frequency estimates for `n ∈ ℕ` and `ω ∈ Ω`. Estimates `est n ω ∈ Θ` form a
minimum-distance estimator for `law` and `freq` if, for every `n` and `ω`, `est n ω` minimizes
`θ ↦ d(law θ, freq n ω)` over all of `Θ`, where `d(f, g) = max_a |f a - g a|` is the sup distance
(`0` when `σ` is empty). With the [empirical site-pattern frequencies](empirical-freq.md) of the
alignment columns as `freq`, it fits the model law to the observed pattern frequencies.
