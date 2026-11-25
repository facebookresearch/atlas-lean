# Lattice bounds from ladder renewal data

Let `P` be a probability measure, `h > 0`, and `X 0, X 1, …` real scores satisfying the
[Cramér conditions](cramer-scores.md) with root `θ`, each almost surely on `hℤ`. Given a
[ladder input](ladder-input.md) for their [maximal segment scores](max-segment-score-rv.md) `Mₙ`,
with excursion heights almost surely on `hℤ` and mean excursion length `A > 0`, and
[lattice ladder renewal data](lattice-ladder-renewal-data.md) with span `h` for its first excursion
height, for every real `x` and every `ε > 0`, eventually
`exp(-K e^{-θ x}) - ε ≤ P(Mₙ ≤ log n / θ + x) ≤ exp(-K e^{-θ (x + h)}) + ε`, with `K = C / A` and
`C = e^{θ h} C_∞ (1 - E e^{θ D})` the [lattice excursion-height renewal constant](tail-const-2.md).
