# Binomial bounds on the sign-test tail

Let `Γ ≥ 1`, and let the success probabilities
`π_i`, `i < n`, of independent Bernoulli variables `B_i` satisfy
`1 / (1 + Γ) ≤ π_i ≤ Γ / (1 + Γ)` for every `i`. Then for every `k`,
`P(Bin(n, 1 / (1 + Γ)) ≥ k) ≤ P(∑ᵢ Bᵢ ≥ k) ≤ P(Bin(n, Γ / (1 + Γ)) ≥ k)`, where
`P(∑ᵢ Bᵢ ≥ k)` is the Poisson-binomial upper tail `poissonBinomialTail π k` and the binomial tails
are the Poisson-binomial tails with constant success probabilities.

## Sources

- P. R. Rosenbaum, "Sensitivity analysis for certain permutation inferences in matched observational studies", Biometrika 74 (1987) 13–26; P. R. Rosenbaum, *Observational Studies*, 2nd ed., Springer (2002), §4.3.
