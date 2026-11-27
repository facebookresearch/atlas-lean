# Lattice scores: no Gumbel limit for the maximal segment score

Let `P` be a probability measure and `R` a [lattice renewal input](lattice-renewal-input.md) for
the scores `X 0, X 1, …`: i.i.d. scores on the lattice `hℤ` with `h > 0` satisfying the
[Cramér conditions](cramer-scores.md) with root `θ > 0`, a [ladder input](ladder-input.md) for
their maximal segment scores with mean excursion length `A > 0` and excursion heights on `hℤ` with
distribution function `F`, and the lattice renewal tail `(1 - F(k h)) e^{θ (k + 1) h} → C`, where
`C > 0`. Then for every real `x`, `P(Mₙ ≤ log n / θ + x)` converges to no limit as `n → ∞`, where
`Mₙ` is the [maximal segment score](max-segment-score-rv.md) of the first `n` scores.
