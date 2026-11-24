# Rare-disease limit

**Rare-disease limit** (VanderWeele et al. 2010). Let `G` and `E` be independent in the
population with `P(G = 1) = π_G ∈ (0, 1)` and `P(E = 1) = π_E ∈ (0, 1)`, and let the disease risk
in cell `(G, E) = (i, j)` be `ε ρ_{ij}` with `ρ_{00} = 1` and positive relative risks
`ρ_{10}, ρ_{01}, ρ_{11}`. Write the cell masses as risk times population frequency for cases and
`(1 - risk)` times frequency for non-cases. Then the odds-ratio interaction tends to
`ρ_{11} / (ρ_{10} ρ_{01})`, the risk-ratio interaction, as `ε → 0⁺`.

## Sources

- VanderWeele et al. (2010), Background and Appendix A (the rare-disease approximation), derived as a limit.
