# The chosen maximizer is a maximum-likelihood estimator

Let `Θ` be a nonempty compact topological space, `σ` a finite set and `law : Θ → (σ → ℝ)` continuous
with `law θ a > 0` for all `θ` and `a`. For any frequency estimates `freq n ω : σ → ℝ`, the
[estimate `est n ω` chosen by the extreme value theorem](mle.md) is a
[maximum-likelihood estimator](is-mle.md): `L(freq n ω, θ) ≤ L(freq n ω, est n ω)` for every `n`,
`ω` and `θ`, where `L` is the [log-likelihood criterion](log-lik.md).
