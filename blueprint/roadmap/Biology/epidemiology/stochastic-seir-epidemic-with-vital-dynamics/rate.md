# Rate

The **intensity of channel `c` at time `x`** along the count paths `(S, E, I, R)` at
population scale `N`, in Kurtz's density-dependent form
`N · λ_c(S(x) / N, E(x) / N, I(x) / N, R(x) / N)`. For `N > 0` these are the Markov rates
`μ N`, `β S I / N`, `σ E`, `γ I`, `μ S`, `μ E`, `μ I`, `μ R` (`rate_birth`, `rate_infection`,
…).
