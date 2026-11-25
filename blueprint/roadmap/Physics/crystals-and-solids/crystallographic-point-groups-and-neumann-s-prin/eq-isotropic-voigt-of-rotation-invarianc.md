# Swap, quarter-turn and 45° invariance make a Voigt matrix isotropic

Let `C` be a real `6 × 6` matrix with `Cᵀ = C` that is invariant under the three axis swaps,
`C_{IJ} = C_{π(I) π(J)}` for the [x ↔ y](voigt-swap01.md), [x ↔ z](voigt-swap02.md) and
[y ↔ z](voigt-swap12.md) index permutations `π`, under the quarter-turn about `z` in entry form,
`C_{IJ} = s_I s_J C_{ρ(I) ρ(J)}` with the [permutation](voigt-rot-z90.md) `ρ` and the
[signs](voigt-rot-z90-sign.md) `s`, and under the [action](voigt-rotate.md) of the
[rotation by 45° about the z-axis](rz45.md). Then `C` is the
[isotropic Voigt matrix](isotropic-voigt.md) with `λ = C₁₂` and `μ = C₄₄`. Voigt indices `1, …, 6`
label the axis pairs `xx`, `yy`, `zz`, `yz`, `xz`, `xy`, in this order.
