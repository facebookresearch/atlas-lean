# The marginal law of the phenotype given the causal variant

If `y = x β + e` with
`β ~ N(0, σ₀²)` independent of `e ~ N(0, σ² I)`, then `y` has density
`multivariateGaussianPDFReal 0 (serCov σ2 σ02 x)`.
