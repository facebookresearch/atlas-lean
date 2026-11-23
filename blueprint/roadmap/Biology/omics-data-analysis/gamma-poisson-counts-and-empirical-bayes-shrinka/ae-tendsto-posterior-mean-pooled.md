# Almost-sure limit of the posterior-moment expressions at pooled counts

Let the cell
counts `X₀, X₁, …` (natural numbers) be pairwise independent and identically distributed, with
integrable mean `E X₀ = s r₀` for a common size factor `s > 0` (e.g. `Xⱼ ~ Po(s r₀)` at a true
rate `r₀`). Then for arbitrary real `a, b`, almost surely `(a + K) / (b + S)` tends to `r₀` and
`(a + K) / (b + S) ^ 2` tends to `0`, where `K` and `S = n s` are the pooled count and exposure
of the first `n` cells. For a valid prior `a, b > 0` these are the mean and variance of the
pooled posterior `Gamma(a + K, b + S)`, so the result is then almost-sure posterior
consistency.
