# Ld sum inequality

`ld_sum_inequality`: `log₂ x + log₂ y + 2 ≤ 2 log₂ (x + y)` for
`x, y > 0`. Isabelle proves it via `4xy ≤ (x + y)²` and `powr`;
here via `Real.logb_le_logb`.
