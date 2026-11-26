# Threshold of the matched-filter test

For a finite index set `ι`, means `s₀, s₁ ∈ ℝ^ι`, a real `ι × ι` matrix `R`, priors `π₀`, `π₁` and
costs `C₀₀`, `C₀₁`, `C₁₀`, `C₁₁` (`C_ij` the cost of deciding `i` when the truth is `j`), the
threshold is `log(π₀ (C₁₀ - C₀₀) / (π₁ (C₀₁ - C₁₁))) + (s₁ᵀ R⁻¹ s₁ - s₀ᵀ R⁻¹ s₀) / 2`. It is defined
for all inputs with the conventions `a / 0 = 0`, `log 0 = 0`, `log a = log |a|` and `R⁻¹ = 0` for
singular `R`; the intended domain is `π₀, π₁ > 0`, `C₀₀ < C₁₀`, `C₁₁ < C₀₁` and `R` positive
definite.
