# First-order law of propagation of uncertainty, correlated inputs

If the measurement
function `f` has Fréchet derivative `f'` at the input estimate `x`, the variance of the
first-order Taylor linearization `ω ↦ f x + f' (X ω - x)` is
`∑ i, ∑ j, cᵢ * cⱼ * cov[X i, X j]`, where `cᵢ = ∂f/∂xᵢ (x) = fderiv ℝ f x (Pi.single i 1)` are
the sensitivity coefficients. It is `measurementFunction_variance_affineCombination` applied to
the coefficients `f' (Pi.single i 1)`, which equal `cᵢ` by `HasFDerivAt.fderiv`. The identity is
exact for the linearization only; for a nonlinear `f` it is not a statement about the variance of
`f X`, whose deviation from the linearization is controlled by
`measurementFunction_firstOrder_remainder_le`.
