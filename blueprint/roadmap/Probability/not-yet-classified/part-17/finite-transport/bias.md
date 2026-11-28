# Expectation gap of a score

For weight vectors `S T : V → ℝ` and a score
`f : V → ℝ` on a finite type, `bias S T f = |∑ x, S x * f x - ∑ x, T x * f x|`, the
absolute difference of the weighted score sums. When `S` and `T` are probability
distributions (nonnegative entries summing to `1`) it is the gap between the expectations
of `f` under `S` and under `T`; for other weights it need not be an expectation gap.
