# Overdispersion gives a solution of the score equations, heterogeneous size factors

Let
`μ̂ = (∑ᵢ kᵢ) / (∑ᵢ sᵢ)` be the pooled Poisson rate and `sᵢ μ̂` the fitted Poisson means. If the
Pearson-type excess `∑ᵢ (kᵢ - sᵢ μ̂)² > ∑ᵢ kᵢ` holds (residual sum of squares above the summed
Poisson variances; at a common size factor this is `M < V`, see `overdispersed_const_iff`), then
the joint score equations have a solution `(â, b̂)` with `â, b̂ > 0`. At a common size factor it
is unique (`existsUnique_score_root_const_varying`); at heterogeneous size factors it need not be
(`exists_two_score_roots` and the tests). That a solution maximizes the likelihood is not proved
here.
