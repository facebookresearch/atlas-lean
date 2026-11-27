# Matching variables drop out

**Matching variables drop out** (Breslow and Day 1980, p. 251). For a matched set of `M + 1`
subjects with exposures `x_i ∈ ℝ^K`, independent outcomes with `P(y_i = 1) = σ(α + β · x_i)`,
every intercept `α`, coefficient vector `β` and vector `z ∈ ℝ^K` common to the whole set, the
conditional probability that subject `j` is the case given exactly one case is unchanged when
every exposure `x_i` is replaced by `x_i + z`.
Here `σ` is the logistic function `Real.sigmoid`.

## Sources

- Breslow and Day (1980), p. 251.
