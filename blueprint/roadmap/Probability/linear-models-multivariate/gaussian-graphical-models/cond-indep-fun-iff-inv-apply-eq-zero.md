# Pairwise Markov property of Gaussian vectors

If `V = (X₀, X₁, Y) ~ N(μ, S)` with `S`
positive definite, then `X₀` and `X₁` are conditionally independent given `Y` iff
`(S⁻¹)₀₁ = 0`. (The standard Borel sample space is the setting of Mathlib's conditional
independence.)
