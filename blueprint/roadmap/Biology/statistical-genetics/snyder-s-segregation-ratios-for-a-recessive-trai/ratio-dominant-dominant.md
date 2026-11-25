# Snyder's `R`

The probability that a child of a dominant × dominant mating is recessive,
for parents drawn independently from the Hardy–Weinberg law: both parents must transmit `t`,
independently. It is a quotient by `(dominantFreq q)²` with `dominantFreq q = 1 - q²`, which is
positive exactly for `q < 1` when `0 ≤ q ≤ 1`, the intended domain. At `q = 1` the denominator
vanishes and the value is `0`, since Lean's division is total (`x / 0 = 0`).
