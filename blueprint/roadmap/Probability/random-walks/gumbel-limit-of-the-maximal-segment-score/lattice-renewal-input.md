# Renewal input for lattice scores

For a measure `P` on `Ω` and real random scores `X 0, X 1, …`, a lattice renewal input consists of
reals `θ` and `h > 0`, the [Cramér conditions](cramer-scores.md) for the scores with root `θ`, the
condition that every `X i` lies almost surely on the lattice `hℤ`, a
[ladder input](ladder-input.md) for their
[maximal segment scores](max-segment-score-rv.md) `Mₙ` whose excursion heights `Y i` lie almost
surely on `hℤ`, with distribution function `F`, and a real `C` with
`(1 - F(k h)) e^{θ (k + 1) h} → C` as `k → ∞` over the natural numbers, the lattice renewal tail
`P(Y ≥ (k + 1) h) ~ C e^{-θ (k + 1) h}`. The limit theorems use the ladder input, the lattice
condition on the excursion heights, the tail, `h > 0` and `θ > 0` from the Cramér conditions, and
the calibration result also uses the measurability of the scores; the lattice condition on the
scores records the setting and is not used.
