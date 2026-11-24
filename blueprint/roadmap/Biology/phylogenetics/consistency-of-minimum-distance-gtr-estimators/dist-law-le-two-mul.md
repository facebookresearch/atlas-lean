# The fitted law lies within twice the frequency error of the true law

Let `σ` be a finite set, `law` a map from a set `Θ` to the functions `σ → ℝ`, and `est` a
[minimum-distance estimator](is-min-dist-estimator.md) for `law` and frequency estimates
`freq n ω : σ → ℝ`. For every `θ₀ ∈ Θ`, every `n` and every `ω`,
`d(law (est n ω), law θ₀) ≤ 2 d(freq n ω, law θ₀)`, where `d` is the sup distance on `σ → ℝ`. No
topology on `Θ` is needed: the bound follows from the triangle inequality and the minimality of
`est n ω`.
