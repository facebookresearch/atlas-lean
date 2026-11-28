# Mean-square end-to-end distance

**Mean-square end-to-end distance** (Kratky and Porod 1949). Let `(Ω, P)` be a probability
space and `u : Ω → ℝ → ℝ³` a random tangent field that is jointly measurable, has unit length
`‖u ω s‖ = 1` everywhere, and has correlation `E ⟪u(s), u(s')⟫ = e^{-|s - s'|/ℓ_p}` for all
`s, s' ∈ [0, L]`, with `ℓ_p > 0` and `L ≥ 0`. Then the end-to-end vector
`R = ∫_0^L u(s) ds` satisfies `E ‖R‖² = 2 ℓ_p L - 2 ℓ_p² (1 - e^{-L/ℓ_p})`.

## Sources

- Kratky and Porod (1949); Tokmakoff, Section 9.2.
