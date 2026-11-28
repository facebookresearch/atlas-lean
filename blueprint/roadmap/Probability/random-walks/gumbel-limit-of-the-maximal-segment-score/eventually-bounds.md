# Lattice scores: liminf and limsup bounds for the maximal segment score

Let `P` be a probability measure and `R` a [lattice renewal input](lattice-renewal-input.md) for
the scores `X 0, X 1, …`: i.i.d. scores on the lattice `hℤ` with `h > 0` satisfying the
[Cramér conditions](cramer-scores.md) with root `θ > 0`, a [ladder input](ladder-input.md) for
their maximal segment scores with mean excursion length `A > 0` and excursion heights on `hℤ` with
distribution function `F`, and the lattice renewal tail `(1 - F(k h)) e^{θ (k + 1) h} → C`. Then
for every real `x` and every `ε > 0`, eventually
`exp(-K e^{-θ x}) - ε ≤ P(Mₙ ≤ log n / θ + x) ≤ exp(-K e^{-θ (x + h)}) + ε`, where `K = C / A` is
the [constant of the lattice bounds](k-2.md) and `Mₙ` the
[maximal segment score](max-segment-score-rv.md) of the first `n` scores.
