# Normal limit of an asymptotically linear estimator (scalar)

If
`√n (θ̂ₙ - θ) = n^{-1/2} ∑ φ(Xᵢ) + oₚ(1)` with `φ` an influence function (integrable,
square integrable, mean zero), then `√n (θ̂ₙ - θ) ⇒ N(0, E φ²)`: the CLT
(`tendstoInDistribution_inv_sqrt_mul_sum_sub`) gives the limit for the linear part and
Slutsky (`tendstoInDistribution_of_tendstoInMeasure_sub`) removes the remainder. The
`oₚ(1)` remainder is an explicit hypothesis; a cross-fitted nuisance product-rate
`oₚ(n^{-1/2})` bound discharging it is a separate obligation, not proved here.
