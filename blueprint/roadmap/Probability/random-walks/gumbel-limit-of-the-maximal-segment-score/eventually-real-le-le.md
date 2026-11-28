# Extreme-value upper bound from a ladder input

Let `P` be a probability measure, a [ladder input](ladder-input.md) under `P` for statistics `M n`,
with excursion-height distribution function `F` and mean excursion length `A > 0`, a filter `L` on
the natural numbers finer than the cofinite one, thresholds `t n` and reals `c_lo` and `c_hi`.
Suppose that for every `δ > 0`, eventually along `L`, `c_lo - δ ≤ n (1 - F(t n)) ≤ c_hi + δ`. Then
for every `ε > 0`, eventually along `L`, `P(M n ≤ t n) ≤ exp(-c_lo / A) + ε`. The upper bound `c_hi`
is used only to get `1 - F(t n) → 0`.
