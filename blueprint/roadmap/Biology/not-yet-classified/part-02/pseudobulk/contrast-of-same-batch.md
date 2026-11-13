# Identification away from the boundary

One pair of donors in the same batch whose
condition indicators differ by one identifies `τ` from the mean-zero-noise expectations. Under
perfect confounding (`batch = a + b · cond`, `b ≠ 0`) no such pair exists. Such a pair is
sufficient, not necessary: the batch covariate enters linearly, so for `batch = ![0, 1, 2]` and
`cond = ![0, 1, 1]` no two donors share a batch, yet `(m₁ - m₀) - (m₂ - m₁) = τ` for the donor
means `mᵢ`.
