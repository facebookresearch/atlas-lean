# Tajima's `D`

**Tajima's `D`** (Tajima 1989) for a sample of `n` genes with mean number of pairwise
differences `π` and `S` segregating sites:
`D = (π - S / a₁) / √(e₁ S + e₂ S (S - 1))`. It is meaningful for `n ≥ 4` and `S ≥ 1`
(`tajimaVarEstimator_pos`); otherwise Lean's junk values for `x / 0` and `√` of a nonpositive
number apply.
