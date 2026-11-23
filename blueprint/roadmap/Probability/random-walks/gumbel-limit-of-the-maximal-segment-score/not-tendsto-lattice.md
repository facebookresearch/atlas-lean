# Lattice case: no Gumbel limit from a ladder input

Let `P` be a probability measure, a [ladder input](ladder-input.md) under `P` for statistics `M n`,
with excursion heights on the lattice `hℤ` almost surely, distribution function `F` and mean
excursion length `A > 0`, and reals `θ > 0`, `h > 0` and `C > 0` with
`(1 - F(k h)) e^{θ (k + 1) h} → C` as `k → ∞`. Then for every real `x`, `P(M n ≤ log n / θ + x)`
converges to no limit: its liminf `exp(-K e^{-θ x})` and limsup `exp(-K e^{-θ (x + h)})`, with
`K = C / A`, differ.
