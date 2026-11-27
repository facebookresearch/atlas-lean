# Competitive exclusion

**Competitive exclusion** (Hsu, Hubbell and Waltman 1977, Theorem 3.3): let `S⁰ > 0`, `D > 0`,
and for every species `i` let `mᵢ, aᵢ, yᵢ > 0` and `mᵢ > D`. Suppose species `i₀` has break-even
concentration `λ_{i₀} < S⁰`, and every other species `j ≠ i₀` has `λ_{i₀} < λⱼ`; losing species
may share a break-even concentration, at any level. Then every solution `(S, x)` of the
chemostat on `[0, ∞)` with `S(0) > 0` and `xᵢ(0) > 0` for every species `i` satisfies, as
`t → ∞`, `S(t) → λ_{i₀}`, `x_{i₀}(t) → y_{i₀} (S⁰ - λ_{i₀})`, and `xⱼ(t) → 0` for every
`j ≠ i₀`. With `bᵢ = mᵢ / D`, and the species relabeled so that `i₀` comes first and the
break-even concentrations are nondecreasing, these are Hsu, Hubbell and Waltman's hypothesis
(Hₙ), `0 < λ₁ < λ₂ ≤ ⋯ ≤ λₙ`, `λ₁ < S⁰` and `bᵢ > 1`, and the initial conditions
`S(0) > 0`, `xᵢ(0) > 0` of their system (2.1)ₙ.

## Sources

- Hsu, Hubbell and Waltman (1977), system (2.1)ₙ (p. 368), hypothesis (Hₙ) and Theorem 3.3 (p. 369).
