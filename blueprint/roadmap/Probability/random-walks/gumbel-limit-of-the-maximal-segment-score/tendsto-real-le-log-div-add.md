# Gumbel limit from a ladder input with an exponential excursion tail

Let `P` be a probability measure, a [ladder input](ladder-input.md) under `P` for statistics `M n`,
with excursion-height distribution function `F` and mean excursion length `A > 0`, and `θ > 0` and
`C` reals with `(1 - F(t)) e^{θ t} → C` as `t → ∞`, the exponential tail `P(Y > t) ~ C e^{-θ t}`
that the renewal theorem gives in the nonlattice case. Then for every real `x`,
`P(M n ≤ log n / θ + x) → exp(-K e^{-θ x})` with `K = C / A` (Iglehart 1972; Karlin and Dembo 1992,
Theorem 1).
