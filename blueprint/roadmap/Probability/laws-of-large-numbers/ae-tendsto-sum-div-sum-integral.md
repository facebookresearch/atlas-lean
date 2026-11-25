# Strong law for nonnegative, non-identically distributed variables

Let `Y₀, Y₁, …` be
pairwise independent, a.e. nonnegative, square-integrable real random variables whose means
`mᵢ = E Yᵢ` are bounded by `B`, whose variances satisfy `Var Yᵢ ≤ C mᵢ`, and whose total mean
`Mₙ = ∑_{i<n} mᵢ` diverges. Then almost surely `(∑_{i<n} Yᵢ) / Mₙ → 1`.

For Poisson counts `Yᵢ ~ Po(mᵢ)` the variance hypothesis holds with `C = 1`. The proof is the
Chebyshev–Borel–Cantelli argument along a subsequence with `M_{σ(k)} ≈ k²`, followed by
bracketing, as in `ProbabilityTheory.pairwise_indep_slln` (the indicator case, `C = B = 1`).
