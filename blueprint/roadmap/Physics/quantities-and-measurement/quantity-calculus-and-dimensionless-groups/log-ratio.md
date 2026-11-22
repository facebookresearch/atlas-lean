# Log Ratio

The natural logarithm `ln (x / x₀)` of the ratio of a positive value `x` to a positive
reference value `x₀` of the same dimension `d`, such as `ln (c / c°)` for a concentration `c`
and a standard concentration `c°`. Only ratios of two positive values of one dimension are
accepted, so there is no logarithm of a single dimensioned value; that `x` and `x₀` have the
same dimension is enforced by their type `WithDim d ℝ`.
