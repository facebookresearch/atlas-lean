# Swap and quarter-turn invariance make a Voigt matrix cubic

Let `C` be a real `6 × 6` matrix with `Cᵀ = C` that is invariant under the three axis swaps,
`C_{IJ} = C_{π(I) π(J)}` for the [x ↔ y](voigt-swap01.md), [x ↔ z](voigt-swap02.md) and
[y ↔ z](voigt-swap12.md) index permutations `π`, and under the quarter-turn about `z` in entry form,
`C_{IJ} = s_I s_J C_{ρ(I) ρ(J)}` with the [permutation](voigt-rot-z90.md) `ρ` and the
[signs](voigt-rot-z90-sign.md) `s`. Then `C` is the [cubic Voigt matrix](cubic-voigt.md) with
`c₁₁ = C₁₁`, `c₁₂ = C₁₂` and `c₄₄ = C₄₄`. Voigt indices `1, …, 6` label the axis pairs `xx`, `yy`,
`zz`, `yz`, `xz`, `xy`, in this order. The quarter-turn condition matters: the axis swaps alone
allow nonzero couplings `C₁₄ = C₂₅ = C₃₆` between normal and shear entries.
