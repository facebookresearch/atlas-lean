# Consistency of a root of the joint score equations (Cramér), heterogeneous size factors

Let `(S₀, X₀), (S₁, X₁), …` be pairwise independent, identically distributed pairs of a positive
size factor and a count, both integrable, and let the true hyperparameters `a₀, b₀ > 0` solve the
population rate equation, `popRateScoreLog μ S₀ X₀ a₀ b₀ = 0` (which follows from the conditional
mean, `popRateScoreLog_eq_zero_of_condMean`). Assume local identifiability of the shape: for all
small `η > 0` there are rates at which the population rate and shape scores are both positive at
the shape `a₀ - η`, and rates at which both are negative at `a₀ + η` (a sign change of the
population profile shape score at `a₀`, stated without the population rate root). Then almost
surely, for every `ε > 0` and all large `n`, the score equations of the first `n` cells have a
solution `(â, b̂)` with `|â - a₀| < ε` and `|b̂ - b₀| < ε`.

The sign hypothesis is assumed, not derived from the negative binomial law: it rests on the
expected shape score vanishing at the truth, which is not proved here or in
`HierarchicalCountMLE`.
