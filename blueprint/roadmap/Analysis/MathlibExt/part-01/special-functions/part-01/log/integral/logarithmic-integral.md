---
article_id: af_7461e37aede83cec318d2063
declaration: def
origin: cited
statement: formalized
lean: Real.logarithmicIntegral
---

# Logarithmic Integral

Normalized Cauchy-principal-value logarithmic integral `li`.

For `0 ≤ x < 1`, `li x = ∫ t in 0..x, (log t)⁻¹`. For `x > 1`,
`li x = (∫ u in 0..1, ((log (1 - u))⁻¹ + (log (1 + u))⁻¹)) +
        ∫ t in 2..x, (log t)⁻¹`,
where the first integral is the paired symmetric principal value
`PV ∫₀² dt / log t = ∫₀¹ ((log (1-u))⁻¹ + (log (1+u))⁻¹) du` obtained
by `t = 1 ∓ u`. The value at `0` is `0`. The function is not defined at
`1` because the integrand is singular there. Single-point totalizations
`(log 1)⁻¹ = 0` and `(log 0)⁻¹ = 0` do not affect Lebesgue interval
integrals.

## Depends on

- [Logarithmic Integral Domain](logarithmic-integral-domain.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.Log.Integral](../../../../../../../../sources/v2/MathlibExt.md)
- arXiv:2306.14073v1 and arXiv:2309.16007v1, normalized lower limit `0` and Cauchy principal value at `t = 1` via symmetric pairing.
