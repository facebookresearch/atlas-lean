# Lattice liminf and limsup bounds from a ladder input

Let `P` be a probability measure, a [ladder input](ladder-input.md) under `P` for statistics `M n`,
with excursion heights `Y i`, distribution function `F` and mean excursion length `A > 0`, and reals
`θ > 0`, `h > 0` and `C`. Suppose every `Y i` lies almost surely on the lattice `hℤ` and
`(1 - F(k h)) e^{θ (k + 1) h} → C` as `k → ∞` over the natural numbers, the lattice renewal tail
`P(Y > k h) = P(Y ≥ (k + 1) h) ~ C e^{-θ (k + 1) h}`. Then with `K = C / A`, for every real `x` and
every `ε > 0`, eventually
`exp(-K e^{-θ x}) - ε ≤ P(M n ≤ log n / θ + x) ≤ exp(-K e^{-θ (x + h)}) + ε`; that is, the liminf is
at least `exp(-K e^{-θ x})` and the limsup at most `exp(-K e^{-θ (x + h)})` (Karlin and Dembo 1992,
Theorem 1, lattice case).
