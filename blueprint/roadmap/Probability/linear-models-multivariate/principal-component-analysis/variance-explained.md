# Proportion of variance explained by principal components

The proportion of total sample variance explained by the first `k` principal components:
`(λ₀ + ⋯ + λ_{k-1}) / tr S` for the sample covariance matrix `S`. The junk value `0` is
returned when the total variance `tr S` is `0` (constant data).
