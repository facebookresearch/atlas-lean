# Unconditional Cramér–Lundberg limit for the `Exp(1)` tilted family

Assume `∀ t, Z t = (Ici 0).indicator (fun s => (ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ)).real (Ioi s)) t + ∫ y, Z (t - y) ∂(ENNReal.ofReal (1 + θ)⁻¹ • expMeasure (1 + θ))`.

For
`θ > 0` let `G_θ = (1 + θ)⁻¹ · Exp(1 + θ)`. If `Z` is measurable, bounded, zero on
`(-∞, 0)` and solves `Z t = 1_{t ≥ 0} G_θ(t, ∞) + ∫ Z (t - y) dG_θ(y)`, then
`e^{θ t} Z t → (1 + θ)⁻¹`. (For the maximum `M` of the ladder process,
`P(M > t) = (1 + θ)⁻¹ e^{-θ t}` exactly: a geometric sum of `Exp(1 + θ)` ladder
heights with continuation probability `(1 + θ)⁻¹`.)
