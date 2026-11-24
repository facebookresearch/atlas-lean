# Pooled Gamma–Poisson conjugacy

For `a > 0`, `b > 0`, a finite set of cells `j` with size factors `sⱼ > 0`, counts `kⱼ ∈ ℕ`,
`K = ∑ⱼ kⱼ` and `S = ∑ⱼ sⱼ`, and every real `r`, `L(k ∣ r) g_{a,b}(r) / m(k) = g_{a+K, b+S}(r)`,
with the Gamma density `g_{α,β}(r) = β^α r^(α−1) e^(−β r) / Γ(α)` for `r ≥ 0`, and `0` for `r < 0`,
the [joint likelihood](pooled-lik.md) `L` and the
[joint marginal likelihood](pooled-marginal-lik.md) `m`. With the prior `λ ~ Gamma(a, b)` and
conditionally independent cell counts `kⱼ ~ Po(sⱼ λ)`, the posterior density of `λ` is therefore the
`Gamma(a + K, b + S)` density; with no cells it is the prior.

## Sources

- A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, D. B. Rubin, *Bayesian Data
  Analysis*, 3rd ed., CRC Press (2013), §2.6.
