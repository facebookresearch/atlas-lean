# Multivariate hypergeometric mass function

For a finite set `ι` of colours, `R ∈ ℕ` and counts `n, r : ι → ℕ`, let
`H(R; n, r) = ∏ᵢ C(nᵢ, rᵢ) / C(∑ᵢ nᵢ, R)` if `∑ᵢ rᵢ = R`, and `H(R; n, r) = 0` otherwise. Since
`C(a, b) = 0` for `b > a`, the value is `0` when some `rᵢ > nᵢ`; this covers `R > ∑ᵢ nᵢ`, where the
denominator also vanishes and `x / 0 = 0`. For `∑ᵢ rᵢ = R ≤ ∑ᵢ nᵢ`, `H(R; n, r)` is the probability
that `R` draws without replacement from an urn with `nᵢ` balls of colour `i` give the colour counts
`r`.
