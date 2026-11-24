# Normal limit of an asymptotically linear estimator (vector)

If
`√n (θ̂ₙ - θ) = n^{-1/2} ∑ φ(Xᵢ) + oₚ(1)` with `φ` an influence function (integrable,
square integrable, mean zero), then `√n (θ̂ₙ - θ) ⇒ Y` with `⟪Y, t⟫ ~ N(0, E ⟪φ, t⟫²)`: the
multivariate CLT (`tendstoInDistribution_inv_sqrt_smul_sum_comp`) plus Slutsky. As in
the scalar case, the `oₚ(1)` remainder (in particular any cross-fitted nuisance
product-rate bound) is an explicit hypothesis, not proved here.
