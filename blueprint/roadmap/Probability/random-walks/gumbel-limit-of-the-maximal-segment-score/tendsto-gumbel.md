# Gumbel limit for the maximal segment score of nonlattice scores

Let `P` be a probability measure and `R` a [nonlattice renewal input](nonlattice-renewal-input.md)
for the scores `X 0, X 1, …`: i.i.d. nonlattice scores satisfying the
[Cramér conditions](cramer-scores.md) with root `θ > 0`, a [ladder input](ladder-input.md) for
their maximal segment scores with mean excursion length `A > 0` and excursion-height distribution
function `F`, and the renewal tail `(1 - F(t)) e^{θ t} → C`. Then for every real `x`,
`P(Mₙ ≤ log n / θ + x) → exp(-K e^{-θ x})` as `n → ∞`, where `K = C / A` is the
[Gumbel constant](k.md) and `Mₙ` the [maximal segment score](max-segment-score-rv.md) of the first
`n` scores.
