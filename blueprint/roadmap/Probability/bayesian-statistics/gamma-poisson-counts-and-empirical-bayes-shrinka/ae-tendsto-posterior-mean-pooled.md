# Almost-sure limit of the posterior-moment expressions at pooled counts

Let `μ` be a probability measure, `s > 0`, `r₀` real, and `X₀, X₁, …` random variables with values
in `ℕ` that are pairwise independent and identically distributed, with `X₀` integrable and
`E X₀ = s r₀` (e.g. `Xⱼ ~ Po(s r₀)`). Then for all real `a` and `b`, almost surely
`(a + Kₙ) / (b + n s) → r₀` and `(a + Kₙ) / (b + n s)² → 0`, where `Kₙ = ∑_{j<n} Xⱼ` and `n s` are
the pooled count and exposure of the first `n` cells. For `a > 0` and `b > 0` these are the mean and
variance of the pooled posterior `Gamma(a + Kₙ, b + n s)`, so the result is then almost-sure
posterior consistency.
