# Consistency of a root of the score equations (Cramér)

Let `X₀, X₁, …` be
pairwise independent, identically distributed counts, observed at a common size factor `σ > 0`,
with mean `E X₀ = σ a₀ / b₀`, the marginal mean of the hierarchy at the true hyperparameters
`a₀, b₀ > 0`. Assume local identifiability of the shape: the population profile shape score
`popProfileShapeScore μ X₀` is positive just left of `a₀` and negative just right of it. Then
almost surely, for every `ε > 0` and all large `n`, the score equations of the first `n` counts
have a solution `(â, b̂)` with `|â - a₀| < ε` and `|b̂ - b₀| < ε`: there is a strongly consistent
sequence of roots of the score equations.

For the negative binomial marginal law the sign hypothesis follows from the identity
`E[∑_{j<X₀} 1 / (a₀ + j)] = log (1 + σ / b₀)` (the expected shape score vanishes at the truth)
together with positivity of the profile information at `a₀`; neither is proved here, so the
crossing is assumed. The tests show the hypotheses can hold together, for a two-point count law
(values `0` and `3`, which is not negative binomial) with `a₀ ∈ (3/10, 1/2)` given by the
intermediate value theorem. The mean hypothesis is the proved marginal mean of `marginalLik`
(`marginalLik_eq_negBinomialReal`, `ProbabilityTheory.hasSum_mul_negBinomialReal`).
