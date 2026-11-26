# Claim 3 in the proof of Cauchy's integral formula: `h ≡ 0`, so the formula holds

Let `f`
be holomorphic on an open set `Ω`, let `γ` be a closed piecewise `C¹` path homologous to zero in
`Ω`, and let `g(z, ζ) = dslope f z ζ`. The function `h` of Claim 2 vanishes on both parts of its
domain `ℂ = Ω ∪ Ω'`:
1. `h(z) = (2πi)⁻¹ ∫_γ g(z, ζ) dζ = 0` for `z ∈ Ω`;
2. `h(z) = (2πi)⁻¹ ∫_γ f(ζ) / (ζ - z) dζ = 0` for `z ∈ Ω'`, the points off `γ` with
   `n(γ, z) = 0`;

and consequently

3. the Cauchy integral formula `n(γ, z) f(z) = (2πi)⁻¹ ∫_γ f(ζ) / (ζ - z) dζ` holds for every `z`
   off `γ`.
