# Univariate Gaussian response to selection, cross-covariance form

Let the breeding value `A` and the phenotype `Z` be real random variables on a probability space,
jointly Gaussian, with `Cov(A, Z) = V_A` and `Var(Z) = V_P > 0`. Let the fitness function `W` be
measurable with `W ≥ 0` and `𝔼[W(Z)] > 0`, and let `W(Z) Z` and `W(Z) A` be integrable. Then
`𝔼[W(Z) A] / 𝔼[W(Z)] - 𝔼[A] = (V_A / V_P) (𝔼[W(Z) Z] / 𝔼[W(Z)] - 𝔼[Z])`: the response is the
selection differential times `Cov(A, Z) / Var(Z)`. When moreover `Var(A) = V_A`, this is the
[breeder's equation](breeding-response-univariate-of-var.md) `R = h² S` with `h² = V_A / V_P`.
