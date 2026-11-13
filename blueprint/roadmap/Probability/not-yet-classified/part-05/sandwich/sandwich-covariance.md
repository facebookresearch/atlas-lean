# Sandwich Covariance

The **sandwich covariance** `A⁻¹ ((B + B†) / 2) A⁻ᵀ` built from a bread (sensitivity)
matrix `A` and a meat (variability) matrix `B`, where `A⁻ᵀ` is the adjoint of
`A⁻¹ = Ring.inverse A`. The meat is symmetrized before sandwiching: only its quadratic
form is identified by the CLT hypotheses, and symmetrization makes the sandwich
self-adjoint (`isSelfAdjoint_sandwichCovariance`) without changing its quadratic form
(`inner_sandwichCovariance_apply`). For a singular `A` the junk value
`Ring.inverse A = 0` gives `0`.
