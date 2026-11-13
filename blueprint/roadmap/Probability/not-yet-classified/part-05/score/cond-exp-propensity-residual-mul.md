# Correct propensity: the augmentation has conditional mean zero

If the candidate
propensity is the true one, `e(X) = μ[1_T | σ(X)]` a.s., then for every bounded measurable
`h`, `E[(1_T - e(X)) h(X) | X] = 0`. With `h = m₁ / e + m₀ / (1 - e)` this is the term that
`aipwScore_eq_ipw_sub` subtracts from the IPW contrast.
