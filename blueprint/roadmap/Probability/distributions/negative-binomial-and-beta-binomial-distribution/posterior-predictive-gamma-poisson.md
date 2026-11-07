# Gamma–Poisson conjugacy, posterior predictive

With prior `Λ ~ Gamma(a, b)`
(`a, b > 0`) and counts `N, N'` that are independent `Po(Λ)` given `Λ`,
`P(N' = j | N = k) = P(N = k, N' = j) / P(N = k) = NB(j; a + k, (a + k) / (b + 1))`.
