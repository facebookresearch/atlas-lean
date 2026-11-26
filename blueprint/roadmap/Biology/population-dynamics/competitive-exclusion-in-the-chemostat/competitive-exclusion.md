# Competitive exclusion

**Competitive exclusion** (Hsu, Hubbell and Waltman 1977, Theorem 3.3; Rapaport and Veruete
2017, Proposition 1 and §3.5): let `S⁰ > 0`, `D > 0`, and for every species `i` let
`mᵢ, aᵢ, yᵢ > 0`. Suppose species `i₀` has `m_{i₀} > D` and break-even concentration
`λ_{i₀} < S⁰`, and every other species `j ≠ i₀` has `mⱼ ≤ D` or (`mⱼ > D` and `λ_{i₀} < λⱼ`).
Then every solution `(S, x)` of the chemostat on `[0, ∞)` with `S(0) ≥ 0` and `xᵢ(0) > 0` for
every species `i` satisfies, as `t → ∞`, `S(t) → λ_{i₀}`, `x_{i₀}(t) → y_{i₀} (S⁰ - λ_{i₀})`,
and `xⱼ(t) → 0` for every `j ≠ i₀`. Hsu, Hubbell and Waltman's Theorem 3.3 assumes in addition
that every `mᵢ > D`, and Rapaport and Veruete's Proposition 1 that the break-even concentrations
are distinct; their §3.5 extends it to ties among the losing species, which the hypotheses here
allow, and a species with `mⱼ ≤ D` has break-even concentration `∞` in their Definition 1.

## Sources

- Hsu, Hubbell and Waltman (1977), Theorem 3.3; Rapaport and Veruete (2017), Definition 1, Proposition 1 and §3.5.
