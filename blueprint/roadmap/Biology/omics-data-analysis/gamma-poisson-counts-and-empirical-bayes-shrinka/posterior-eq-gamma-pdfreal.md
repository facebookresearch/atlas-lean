# Gamma–Poisson conjugacy with exposure

With prior `λ ~ Gamma(a, b)` (`a, b > 0`) and one
count `k ~ Po(s λ)` (`s > 0`), the posterior density (likelihood times prior density over the
marginal likelihood) is the `Gamma(a + k, b + s)` density. At `s = 1` this is
`ProbabilityTheory.gammaPDFReal_posterior`.
