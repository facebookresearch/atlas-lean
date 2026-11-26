# Theta Factor

The factor `[z, z₀; γ a, γ b]` of the theta function attached to `ρ : G →* PGL(2, K₀)` at
`γ : G`. The parameters `a` and `b` are points of the upper half plane, so `pmoebius K₀ (ρ γ) a`
and `pmoebius K₀ (ρ γ) b` are their actual images, never `∞` (`coe_pmoebius_of_mem`); a
`K₀`-rational parameter could be sent to `∞`, which the affine formula cannot represent. When
`z = γ b` or `z₀ = γ a` the denominator vanishes and the factor is `0` (`crossRatio`); when
`z₀ = γ b` the numerator vanishes for every `z`. So the factor is `1` at `z = z₀` exactly when
`z₀ ≠ γ a` and `z₀ ≠ γ b`.
