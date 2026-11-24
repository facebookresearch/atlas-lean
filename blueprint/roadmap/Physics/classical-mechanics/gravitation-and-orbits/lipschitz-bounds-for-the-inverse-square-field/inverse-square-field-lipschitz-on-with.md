# Inverse Square Field lipschitz On With

The exterior Lipschitz bound in Mathlib's standard bundled form:
the inverse-square field is Lipschitz on the exterior set
`{r | rmin ≤ ‖r‖}` with constant `4μ / rmin^3`. This is the form
downstream `LipschitzOnWith` API consumes; the pointwise norm form is
`inverseSquareField_lipschitz_exterior`.
