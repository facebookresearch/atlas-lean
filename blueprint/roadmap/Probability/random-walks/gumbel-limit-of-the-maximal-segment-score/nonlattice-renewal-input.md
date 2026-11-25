# Renewal input for nonlattice scores

For a measure `P` on `Ω` and real random scores `X 0, X 1, …`, a nonlattice renewal input consists
of a real `θ`, the [Cramér conditions](cramer-scores.md) for the scores with root `θ`, the
nonlattice condition (for no `h > 0` does `X 0` lie almost surely on `hℤ`), a
[ladder input](ladder-input.md) for their [maximal segment scores](max-segment-score-rv.md) `Mₙ`,
with excursion-height distribution function `F`, and a real `C` with `(1 - F(t)) e^{θ t} → C` as
`t → ∞`, the renewal tail `P(Y > t) ~ C e^{-θ t}` of the excursion heights. The ladder input and the
tail are the two inputs that renewal theory supplies; the structure takes them as hypotheses. The
[Gumbel limit](tendsto-gumbel.md) uses the ladder input, the tail and `θ > 0` from the Cramér
conditions, and the calibration results built on the structure also use the measurability of the
scores; the nonlattice condition records the setting in which renewal theory provides the tail and
is not used.
