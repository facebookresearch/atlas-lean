# With equal means the matched-filter rule ignores the observation

For a finite index set `ι`, a mean `s ∈ ℝ^ι`, every real `ι × ι` matrix `R`, priors `π₀, π₁ > 0`,
costs with `C₀₀ < C₁₀` and `C₁₁ < C₀₁`, a tie decision and every observation `y`, the
[matched-filter rule](matched-filter-rule.md) with `s₀ = s₁ = s` decides `true` if
`π₀ (C₁₀ - C₀₀) < π₁ (C₀₁ - C₁₁)`, the tie decision if the two are equal, and `false` otherwise.
