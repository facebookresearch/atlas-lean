# Asymptotic coverage of the heteroskedasticity-robust Wald interval

In the i.i.d.
random-design model of `hc0OLSSandwich_tendsto_ae` with measurable regressors and errors, fix a
contrast `c` with nondegenerate robust variance `v = cᵀ Q⁻¹ Ω Q⁻ᵀ c ≠ 0`. If the contrast is
asymptotically normal, `√n (c ⬝ᵥ β̂ₙ - c ⬝ᵥ β) ⟶ N(0, v)` (hypothesis `hAN`, not discharged here),
then the Wald interval `c ⬝ᵥ β̂ₙ ± z √(cᵀ V̂ₙ c) / √n` built from the HC0 sandwich `V̂ₙ` covers
`c ⬝ᵥ β` with probability tending to the standard-normal mass of `[-z, z]`. The consistency of the
robust standard error is proved here from `hc0OLSSandwich_tendsto_ae`; it needs no
homoskedasticity.
