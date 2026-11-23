# Posterior consistency, deterministic core

Along any filter, if the pooled exposure
`S → ∞` and the pooled rate `K / S → r₀`, then for a prior `Gamma(a, b)` with `a, b > 0` the
pooled posterior `Gamma(a + K, b + S)` has mean `(a + K) / (b + S) → r₀`, variance
`(a + K) / (b + S)² → 0`, and assigns vanishing mass to the complement of every neighbourhood
`(r₀ - ε, r₀ + ε)` of `r₀`: the posterior concentrates at `r₀`.
