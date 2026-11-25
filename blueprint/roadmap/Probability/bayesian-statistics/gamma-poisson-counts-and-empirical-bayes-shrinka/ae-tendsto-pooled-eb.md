# Strong consistency of empirical Bayes with pooled counts

Let `ι` be a nonempty finite set of cells with size factors `sⱼ > 0` and total exposure `S = ∑ⱼ sⱼ`,
`a > 0`, `b > 0`, `μ` a probability measure, and `N₀, N₁, …` random variables with values in `ℕ`,
the pooled counts of units `i = 0, 1, …` (e.g. genes or donors), that are pairwise independent and
identically distributed, with `N₀` measurable and `P(N₀ = K) = ∑ m(k)` for every `K ∈ ℕ`, the sum
running over the count vectors `k` with `∑ⱼ kⱼ = K` and `m` the
[joint marginal likelihood](pooled-marginal-lik.md). Then almost surely, for the
[sample mean](sample-mean.md) `M̂ₙ` and the [sample variance](sample-var.md) `V̂ₙ` of
`N₀, …, N_{n−1}`, the [shape estimate](mom-shape.md) `â(M̂ₙ, V̂ₙ)` tends to `a`, the
[rate estimate](mom-rate.md) `b̂(S, M̂ₙ, V̂ₙ)` tends to `b`, and for every pooled count `K` the
[empirical-Bayes posterior mean](eb-posterior-mean.md) at exposure `S` tends to the oracle pooled
posterior mean `(a + K) / (b + S)`.

The Gamma-then-Poisson hierarchy is not constructed as a measure: only the law of `N₀` and the
pairwise independence and identical distribution of the `Nᵢ` are assumed.

## Sources

- C. N. Morris, *Parametric empirical Bayes inference: theory and applications*, J. Amer. Statist.
  Assoc. 78 (1983), 47–55.
