# Known-variance normal location model

Let `X ω : Fin n → ℝ` be the observations, with
`0 < n`, and let `σ > 0` be known. If, under `μ`, the pivot `(x̄ - θ) / (σ / √n)` of the sample
mean has the standard normal law, then the interval `x̄ ± z σ / √n` contains `θ` with
probability `N(0, 1) [-z, z]`. The normal law of the pivot is a hypothesis;
`hasLaw_pivot_of_hasLaw_gaussianReal` derives it from `x̄ ∼ N(θ, σ ^ 2 / n)`, and the law of `x̄`
under i.i.d. normal observations is not derived here.
