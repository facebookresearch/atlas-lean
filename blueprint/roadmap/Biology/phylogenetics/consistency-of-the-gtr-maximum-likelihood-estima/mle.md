# Chosen maximum-likelihood estimator

Let `Θ` be a nonempty compact topological space, `σ` a finite set and `law : Θ → (σ → ℝ)` continuous
with `law θ a > 0` for all `θ` and `a`. For frequency estimates `freq n ω : σ → ℝ`, the chosen
estimate `est n ω` is a point of `Θ` that maximizes the continuous
[log-likelihood criterion](log-lik.md) `θ ↦ L(freq n ω, θ)`. A maximizer exists by the extreme value
theorem; the estimate is one fixed choice among the maximizers.
