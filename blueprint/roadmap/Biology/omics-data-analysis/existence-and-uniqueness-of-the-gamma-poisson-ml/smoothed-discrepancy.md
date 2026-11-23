# Levin and Reeds's function `H`

For counts `k₁, …, kₙ` with sample mean `M`,
`H(u) = ∑ᵢ R_{kᵢ}(u) - n (u² / 2 - max (u - M) 0 ² / 2)` is `∫₀ᵘ (G - F)`, where `G` is the
distribution function of the unit masses at `0, …, kᵢ - 1` (over all `i`) and `F` that of `n`
times Lebesgue measure on `[0, M]`. The profile shape score is a Stieltjes-type transform of
`H` (`profileShapeScore_eq_integral`).
