# Variance of a linear SFS statistic under Kingman's coalescent

`Var(∑_{i=1}^{n-1} a_i ξ_i) = θ ∑_i a_i² / i + (θ / 2)² Var(∑_i a_i L_i)`. The second-order
term needs exactly the variance of the same linear combination of the branch lengths
`L_i = sfsLength n i τ T`, i.e. `∑_{i,j} a_i a_j Cov(L_i, L_j)`
(`variance_sum_eq_sum_covariance`).
