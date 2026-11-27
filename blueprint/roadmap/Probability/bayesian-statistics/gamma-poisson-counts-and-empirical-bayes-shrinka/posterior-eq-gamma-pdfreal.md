# Gamma–Poisson conjugacy with exposure

For `a > 0`, `b > 0`, `s > 0`, `k ∈ ℕ` and every real `r`,
`P(k ∣ r) g_{a,b}(r) / m(k) = g_{a+k, b+s}(r)`, with the Gamma density
`g_{α,β}(r) = β^α r^(α−1) e^(−β r) / Γ(α)` for `r ≥ 0`, and `0` for `r < 0`, the
[Poisson likelihood](poisson-exposure-lik.md) `P(k ∣ r)` and the
[marginal likelihood](marginal-lik.md) `m(k)`. With the prior `λ ~ Gamma(a, b)` and one count
`k ~ Po(s λ)`, the posterior density of `λ` is therefore the `Gamma(a + k, b + s)` density; for
`s = 1` this is the classical Gamma–Poisson conjugacy.

## Sources

- A. Gelman, J. B. Carlin, H. S. Stern, D. B. Dunson, A. Vehtari, D. B. Rubin, *Bayesian Data
  Analysis*, 3rd ed., CRC Press (2013), §2.6.
