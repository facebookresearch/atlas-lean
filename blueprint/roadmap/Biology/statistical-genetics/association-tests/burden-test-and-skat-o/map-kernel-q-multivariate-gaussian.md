# The law of a kernel score statistic is a weighted chi-square mixture

If
`y ~ N(X α, V')` and `K` is symmetric, then `Q_K ~ ∑ⱼ λⱼ χ²₁` with `λ` the eigenvalues of
`(P V'^{1/2})ᵀ K (P V'^{1/2})`. This is T37's `map_skatQ_multivariateGaussian` for an
arbitrary symmetric kernel.
