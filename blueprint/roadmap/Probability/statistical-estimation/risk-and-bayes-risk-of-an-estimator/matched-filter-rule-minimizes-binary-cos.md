# The matched-filter test is Bayes optimal for two Gaussian laws

Let `ι` be a finite index set, `s₀, s₁ ∈ ℝ^ι`, `R` a positive definite `ι × ι` matrix, priors
`π₀, π₁ > 0` with `π₀ + π₁ = 1`, and costs with `C₀₀ < C₁₀` and `C₁₁ < C₀₁`; the truth `0` has law
`N(s₀, R)` and the truth `1` has law `N(s₁, R)`. Then the
[matched-filter rule](matched-filter-rule.md) is measurable, and its deterministic decision has
Bayes risk `π₀ E₀[C(·, 0)] + π₁ E₁[C(·, 1)]` at most that of every randomised decision rule (Markov
kernel from observations to decisions), where `E_j` is the expectation over the decision when the
truth is `j`.
