# Unconditional a.s. consistency of the OLS HC0 sandwich

In the i.i.d. random-design model
`yᵢ = xᵢ ⬝ᵥ β + uᵢ` with `𝔼‖x₀‖⁴ < ∞`, `𝔼[‖x₀‖² u₀²] < ∞`, `𝔼[u₀ x₀] = 0` and a nonsingular
population Gram, the HC0 sandwich computed from the observable OLS residuals converges a.s. to
`Q⁻¹ Ω Q⁻ᵀ`. The three hypotheses `hβ`, `hQ`, `hQinv` of `HC0Sandwich` are discharged.
