# Mcdiarmid product general

McDiarmid on a finite product space, without the positivity
hypothesis: the same one-sided bound as `mcdiarmid_product`, covering
the zero-sensitivity endpoint. When `∑ i, c i ^ 2 = 0` the tail is
actually `0` by `mcdiarmid_product_of_sum_sq_eq_zero`, while the
right-hand side is `Real.exp 0 = 1` by Lean's convention `x / 0 = 0`.
