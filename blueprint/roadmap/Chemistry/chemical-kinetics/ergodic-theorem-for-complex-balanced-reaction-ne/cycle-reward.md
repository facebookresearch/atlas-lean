# Reward collected during a regeneration cycle

For a process `X : ℝ × Ω → σ`, random times `R_0, R_1, … : Ω → ℝ` and an observable
`f : σ → ℝ`, the reward collected by `f` during the `k`-th cycle is the random variable

`W_k(ω) = ∫_{R_k(ω)}^{R_{k+1}(ω)} f(X_s(ω)) ds`,

an oriented interval integral with respect to Lebesgue measure, equal to `0` when `s ↦ f(X_s(ω))` is
not integrable between the two times. For a jointly measurable `X`, `f` the indicator of a
measurable singleton `{x₀}` and `R_k(ω) ≤ R_{k+1}(ω)`, it is the time the path spends in `x₀` during
the cycle.
