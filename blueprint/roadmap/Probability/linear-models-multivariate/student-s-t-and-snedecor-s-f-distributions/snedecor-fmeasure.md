# Snedecor's `F` law

**Snedecor's `F` law** with `(d₁, d₂)` degrees of freedom (Casella–Berger, Definition 5.3.6):
the measure with Lebesgue density
`Γ((d₁ + d₂)/2) / (Γ(d₁/2) Γ(d₂/2)) · (d₁/d₂)^{d₁/2} x^{d₁/2 - 1} (1 + d₁ x / d₂)^{-(d₁+d₂)/2}`
on `x > 0` and `0` elsewhere. It is the law of `(V₁ / d₁) / (V₂ / d₂)` for independent
`V₁ ~ χ²_{d₁}`, `V₂ ~ χ²_{d₂}` (`map_div_chiSquare_eq_snedecorF`). It is a probability
measure for `d₁, d₂ ≥ 1` (`isProbabilityMeasure_snedecorFMeasure`). With zero degrees of freedom
the definition is totalized to the zero measure: if `d₁ = 0` or `d₂ = 0` the normalizing
constant has `Γ(0) = 0` in its denominator, so the density vanishes identically.
