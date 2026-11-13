# Gaussian integral

For `0 < a`, the Gaussian `x ↦ exp (-a * x ^ 2)` is integrable on
`ℝ`, its integral over `ℝ` is `√(π / a)`, and this is also its improper integral:
`∫ x in α..β, exp (-a * x ^ 2) → √(π / a)` as `α → -∞` and `β → ∞` independently.
Integrability is what makes the value meaningful: for `a ≤ 0` the Gaussian is not integrable
(`integrable_exp_neg_mul_sq_iff`), and Mathlib's `integral_gaussian` still reads
`∫ = √(π / a)`, but both sides are the junk value `0`.
