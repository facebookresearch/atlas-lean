# Strong consistency of the rate root, heterogeneous size factors

Let `(S₀, X₀), (S₁, X₁), …`
be pairwise independent, identically distributed pairs of a positive size factor and a count, with
`X₀` integrable, and let `b₀ > 0` solve the population rate equation at the shape `a > 0`,
`popRateScoreLog μ S₀ X₀ a b₀ = 0` (at the true hyperparameters this follows from the conditional
mean, `popRateScoreLog_eq_zero_of_condMean`). Almost surely, for all large `n` the rate root
`b̂ₙ(a)` of the first `n` cells solves their rate score equation, and `b̂ₙ(a) → b₀`.
