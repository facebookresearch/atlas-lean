# Extreme-value lower bound from a ladder input

Let `P` be a probability measure, a [ladder input](ladder-input.md) under `P` for statistics `M n`,
with excursion-height distribution function `F` and mean excursion length `A > 0`, a filter `L` on
the natural numbers finer than the cofinite one, thresholds `t n` and a real `c`. Suppose that for
every `δ > 0`, eventually along `L`, `n (1 - F(t n)) ≤ c + δ`. Then for every `ε > 0`, eventually
along `L`, `exp(-c / A) - ε ≤ P(M n ≤ t n)`.
