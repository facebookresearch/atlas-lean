# First-order law of propagation of uncertainty, correlated inputs

Let `X i` (`i ∈ ι`, a finite index set) be real random variables with finite second moments on a
probability space. If the measurement function `f` has Fréchet derivative `f'` at the input estimate
`x`, the variance of the first-order Taylor linearization `ω ↦ f x + f' (X ω - x)` is
`∑ i, ∑ j, cᵢ * cⱼ * cov[X i, X j]`, where `cᵢ = ∂f/∂xᵢ (x) = f' eᵢ` are the sensitivity
coefficients (`eᵢ` the `i`-th unit vector). It is the
[variance of an affine combination](measurement-function-variance-affine-com.md) applied to these
coefficients. The identity is exact for the linearization only; for a nonlinear `f` it is not a
statement about the variance of `f X`, whose deviation from the linearization is controlled by the
[explicit first-order remainder](measurement-function-first-order-remaind-2.md).
