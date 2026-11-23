# First-order relative uncertainty of products, quotients and powers

Let `X i` (`i ∈ ι`, a finite index set) be real random variables with finite second moments on a
probability space. Let `y = ∏ i, x i ^ p i` with integer exponents `p i` and nonzero input estimates
`x i ≠ 0`. Let the inputs have standard uncertainties `u i` (`Var[X i] = u i ^ 2`) and be
uncorrelated, `cov[X i, X j] = 0` for `i ≠ j`. (Zero covariance is uncorrelatedness, not
independence: dependent variables can have zero covariance. Independence implies uncorrelatedness.)
Then the first-order combined standard uncertainty `u_y`, the standard deviation of the
linearization `ω ↦ y + ∑ i, ∂y/∂xᵢ (x) * (X i ω - x i)`, satisfies
`(u_y / y) ^ 2 = ∑ i, (p i * u i / x i) ^ 2`. It is the
[first-order law for uncorrelated inputs](measurement-function-linearized-variance-3.md) with the
[sensitivity coefficients](fderiv-power-law-single.md) `∂y/∂xᵢ = y * (p i / x i)`. The rule is
first-order: it is exact for the linearization, not for `y` evaluated at random inputs.
