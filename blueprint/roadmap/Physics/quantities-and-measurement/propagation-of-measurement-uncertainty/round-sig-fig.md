# Round Sig Fig

Rounding to `k` significant figures, for a positive count `k : ℕ+`, a reporting function
`ℝ → ℝ`: `roundSigFig k x = round (x * 10 ^ e) / 10 ^ e` with
`e = sigFigShift k x = k - 1 - ⌊log₁₀ |x|⌋`, so the result is an integer multiple of
`10 ^ (-e)`. Ties are rounded upward, since Mathlib's `round x = ⌊x + 1 / 2⌋`; OpenStax §1.5
instead rounds a dropped `5` to an even digit, and the conventions differ only at exact ties.
Significant figures are reporting only, never a substitute for the propagation laws of sections B
and C: see `exists_roundSigFig_add_ne`.
