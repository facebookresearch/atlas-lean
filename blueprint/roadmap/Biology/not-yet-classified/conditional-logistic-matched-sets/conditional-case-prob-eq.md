# The conditional probability is free of the intercept

**The conditional probability is free of the intercept** (Breslow and Day 1980, ch. 7). For
a matched set of `M + 1` subjects with exposures `x_i ∈ ℝ^K`, independent outcomes with
`P(y_i = 1) = σ(α + β · x_i)`, every intercept `α ∈ ℝ` and coefficient vector `β`, the
probability that subject `j` is the case given exactly one case is
`exp(β · x_j) / ∑_i exp(β · x_i)`.
Here `σ` is the logistic function `Real.sigmoid`.

## Sources

- Breslow and Day (1980), p. 251.
