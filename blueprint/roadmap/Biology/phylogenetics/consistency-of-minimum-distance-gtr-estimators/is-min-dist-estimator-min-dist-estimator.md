# The chosen minimizer is a minimum-distance estimator

Let `Θ` be a nonempty compact metric space, `σ` a finite set and `law : Θ → (σ → ℝ)` continuous. For
any frequency estimates `freq n ω : σ → ℝ`, the
[estimate `est n ω` chosen by the extreme value theorem](min-dist-estimator.md) is a
[minimum-distance estimator](is-min-dist-estimator.md):
`d(law (est n ω), freq n ω) ≤ d(law θ, freq n ω)` for every `n`, `ω` and `θ`, where `d` is the sup
distance on `σ → ℝ`.
