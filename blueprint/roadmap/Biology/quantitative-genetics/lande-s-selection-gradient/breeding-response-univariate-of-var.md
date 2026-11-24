# Breeder's equation for a Gaussian breeding value and phenotype

Let the breeding value `A` and the phenotype `Z` be real random variables on a probability space,
jointly Gaussian, with `Cov(A, Z) = V_A`, `Var(A) = V_A` (so `V_A` is the additive genetic
variance) and `Var(Z) = V_P > 0`. Let the fitness function `W` be measurable with `W ≥ 0` and
`𝔼[W(Z)] > 0`, and let `W(Z) Z` and `W(Z) A` be integrable. Then the response
`R = 𝔼[W(Z) A] / 𝔼[W(Z)] - 𝔼[A]` and the selection differential
`S = 𝔼[W(Z) Z] / 𝔼[W(Z)] - 𝔼[Z]` satisfy `R = h² S` with `h² = V_A / V_P`. This is a special
case of the [univariate cross-covariance form](breeding-response-univariate.md), which does not
assume `Var(A) = V_A`.
