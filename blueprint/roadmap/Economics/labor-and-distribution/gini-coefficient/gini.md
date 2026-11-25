# Gini coefficient of a finite income distribution

The Gini coefficient of the income distribution `x` over a finite population of
`n` individuals is the mean absolute difference over twice the mean:
`(∑_i ∑_j |x(i) - x(j)|) / (2 * n * ∑_i x(i))`. It is the usual Gini index when
incomes are nonnegative with positive total; when the total is `0` the division
yields `0` (convention `x / 0 = 0`).
