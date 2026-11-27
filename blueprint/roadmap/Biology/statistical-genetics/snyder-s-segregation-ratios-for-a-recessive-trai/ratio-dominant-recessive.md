# Snyder's `S`

The probability that a child of a dominant × recessive mating is recessive,
for parents drawn independently from the Hardy–Weinberg law. The recessive parent always
transmits `t`, so the child is recessive exactly when the dominant parent transmits `t`. It is a
quotient by the dominant-phenotype frequency `dominantFreq q = 1 - q²`, which is positive exactly
for `q < 1` when `0 ≤ q ≤ 1`, the intended domain. At `q = 1` the denominator vanishes and the
value is `0`, since Lean's division is total (`x / 0 = 0`).
