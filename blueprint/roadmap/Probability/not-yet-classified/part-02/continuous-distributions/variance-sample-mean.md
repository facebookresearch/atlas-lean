# Variance of the sample mean

If `X 0` has a finite second moment and the `X i` are
pairwise independent with the law of `X 0`, then `Var[x̄ₙ] = Var[X 0] / n` for `n ≠ 0`, where
`x̄ₙ` is the canonical sample mean of the first `n` observations. The proof uses Mathlib's
variance of a sum of independent variables, `ProbabilityTheory.IndepFun.variance_sum`.
