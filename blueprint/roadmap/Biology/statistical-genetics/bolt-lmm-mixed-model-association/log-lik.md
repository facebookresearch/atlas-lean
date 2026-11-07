# Marginal log-likelihood of the mean

The marginal log-likelihood of the mean `μ`: the log of the `N(μ, V)` density at `y`,
`-(n log 2π + log det V + (y - μ)ᵀ V⁻¹ (y - μ)) / 2` (`det V > 0` by `posDef_V`).
