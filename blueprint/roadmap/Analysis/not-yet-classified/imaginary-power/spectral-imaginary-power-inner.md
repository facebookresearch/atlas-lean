# Coefficient integral of a spectral imaginary power

Let `H` be a complete complex
Hilbert space, `E : ProjectionValuedMeasure ℝ H` a strongly countably additive PVM, `t :
ℝ`, and `g,h ∈ H`. Then `⟨h,spectralImaginaryPower E t g⟩ = ∫ exp(i t log r) dμ_(g,h)(r)`,
where the finite complex measure is `μ_(g,h)(s)=⟨h,E(s)g⟩`. The inner product is linear in
its second argument.

In this coefficient integral the multiplier is 1 at `r=0`. For `r<0`, `Real.log r=Real.log
|r|`, so the integrand is `exp(i t log |r|)`. If `E` is concentrated at zero,
`spectralImaginaryPower E t=I_H` and this coefficient is `⟨h,g⟩`.
