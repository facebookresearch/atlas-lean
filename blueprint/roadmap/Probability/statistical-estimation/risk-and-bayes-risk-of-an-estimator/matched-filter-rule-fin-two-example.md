# Two-dimensional example of the matched-filter rule

Take `R` with rows `(2, 1)` and `(1, 2)`, `s₀ = (0, 0)`, `s₁ = (1, 1)`, `π₀ = π₁ = 1/2` and the
costs `C₀₀ = C₁₁ = 0`, `C₀₁ = C₁₀ = 1`. Then `R⁻¹ s₁ = (1/3, 1/3)`, the
[matched statistic](matched-statistic.md) is `(y₁ + y₂) / 3` and the
[threshold](matched-threshold.md) is `log 1 + (2/3) / 2 = 1/3`; the [rule](matched-filter-rule.md)
decides `true` at `(1, 1)`, the tie decision at `(1, 0)` and `false` at `(0, 0)`.
