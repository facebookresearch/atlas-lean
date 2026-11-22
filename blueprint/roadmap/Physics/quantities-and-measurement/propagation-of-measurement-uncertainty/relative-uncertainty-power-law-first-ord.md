# First-order relative-uncertainty rule for products, quotients and powers

Let
`y = ∏ i, x i ^ p i` with integer exponents `p i` and nonzero input estimates `x i ≠ 0`. Let the
inputs have standard uncertainties `u i` (`Var[X i] = u i ^ 2`) and be uncorrelated,
`cov[X i, X j] = 0` for `i ≠ j`. (Zero covariance is uncorrelatedness, not independence: dependent
variables can have zero covariance. Independence implies uncorrelatedness.) Then the first-order
combined standard
uncertainty `u_y`, the standard deviation of the linearization
`ω ↦ y + fderiv ℝ (powerLaw p) x (X ω - x)`, satisfies `(u_y / y) ^ 2 = ∑ i, (p i * u i / x i) ^ 2`.
It is the law `measurementFunction_linearizedVariance_firstOrder_uncorrelated` with the
sensitivity coefficients `y * (p i / x i)` of `fderiv_powerLaw_single`. The rule is first-order:
it is exact for the linearization, not for `y` evaluated at random inputs.
