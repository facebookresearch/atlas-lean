# Risch's recurrence-risk ratio

**Risch's recurrence-risk ratio** `λ_R = K_R / K = P(both affected) / K²`, where
`K = prevalence π f`. The intended domain is a positive prevalence `K > 0`. If `K = 0` the
denominator vanishes and the value is `0`, since Lean's division is total (`x / 0 = 0`).
