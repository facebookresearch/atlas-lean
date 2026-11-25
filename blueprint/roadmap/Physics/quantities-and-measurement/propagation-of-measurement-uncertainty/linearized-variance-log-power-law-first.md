# First-order variance of the logarithm of a power law

Let `X i` (`i ∈ ι`, a finite index set) be real random variables with finite second moments on a
probability space. Let them have variances `Var[X i] = u i ^ 2` and zero covariances,
`cov[X i, X j] = 0` for `i ≠ j`, and let the input estimates be nonzero, `x i ≠ 0`. For the power
law `y(ξ) = ∏ i, ξ i ^ p i` with integer exponents, the linearization of `log |y|` at `x`,
`ω ↦ log |y(x)| + ∑ i, (p i / x i) * (X i ω - x i)`, has variance `∑ i, (p i * u i / x i) ^ 2`: the
sum of the [relative-uncertainty rule](relative-uncertainty-power-law-first-ord.md). Its sensitivity
coefficients `p i / x i` are the partial derivatives of `log |y|` at `x`, the logarithm being
extended to negative arguments by `log y = log |y|`.
