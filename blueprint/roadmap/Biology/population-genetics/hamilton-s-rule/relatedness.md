# Regression relatedness

For real functions `y` (the partner's trait) and `z` (the individual's own trait) on a finite set
of individuals, the regression relatedness is `r = Cov(y, z) / Var(z)`, the regression coefficient
of `y` on `z` (Queller 1992), with the [population covariance](pop-cov.md) `Cov` and the variance
`Var(z) = Cov(z, z)`. It is defined for all `y` and `z`: when `Var(z) = 0` (for instance when `z`
is constant) the convention `x / 0 = 0` makes it `0`; the intended domain is `Var(z) > 0`.
