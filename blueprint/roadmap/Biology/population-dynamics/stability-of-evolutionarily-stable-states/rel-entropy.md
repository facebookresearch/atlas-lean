# Relative entropy Lyapunov function

For a finite set `ι` and vectors `p, y : ι → ℝ`, the function is
`V_p(y) = ∑_i p_i (log p_i - log y_i)`. With the conventions `log 0 = 0` and `log x = log |x|`, it
is defined for all real vectors. For `p` and `y` in the simplex with every `y_i > 0` it is the
relative entropy of `p` with respect to `y`, and for `p_i ≥ 0` and `y_i > 0` it equals
`log P(p) - log P(y)` for the Hofbauer–Sigmund function `P(y) = ∏_i y_i^{p_i}`.
