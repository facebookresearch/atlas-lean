# Calibration of `S / λ̂` is an assumption on `S / λ̂` itself

The estimated-`λ̂` family is a
tail-calibrated family in the sense of `RareVariantInference.MultipleTesting` (reference tail
`χ²₁`) exactly when every null corrected statistic is conservative against `χ²₁`:
`P(S_i / λ̂ ≥ s) ≤ P(χ²₁ > s)` for all `s`. This is not implied by T38's true-`λ` model
(`not_isTailCalibratedFamily_gcStatRV_two`), and it is impossible when every gene is null
(`not_isTailCalibratedFamily_gcStatRV_univ`): it can hold only if some non-null genes inflate
`λ̂`.
