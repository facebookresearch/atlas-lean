# Rounding to k significant figures

Rounding to `k` significant figures, for a count `k ≥ 1`, a reporting function `ℝ → ℝ`:
`x ↦ round (x * 10 ^ e) / 10 ^ e` with `e = k - 1 - ⌊log₁₀ |x|⌋`, so the result is an integer
multiple of `10 ^ (-e)`. It is defined for every real `x`: at `x = 0` the convention
`log₁₀ 0 = 0` gives `e = k - 1`, and the value is `0`. Ties are rounded upward, since
`round t = ⌊t + 1 / 2⌋`; OpenStax §1.5 instead rounds a dropped `5` to an even digit, and the
conventions differ only at exact ties.
Significant figures are a reporting convention, not a substitute for the first-order law of
propagation of uncertainty (see
[rounding is not an uncertainty calculus](exists-round-sig-fig-add-ne.md)).
