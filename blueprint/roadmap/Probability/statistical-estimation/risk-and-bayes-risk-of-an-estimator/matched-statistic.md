# Matched-filter statistic

For a finite index set `ι`, vectors `s₀, s₁ ∈ ℝ^ι` (the two means), a real `ι × ι` matrix `R` and an
observation `y ∈ ℝ^ι`, the matched-filter statistic is `(s₁ - s₀)ᵀ R⁻¹ y`. The matrix inverse is
taken to be `0` when `R` is singular; the intended domain is a positive definite covariance `R`.
