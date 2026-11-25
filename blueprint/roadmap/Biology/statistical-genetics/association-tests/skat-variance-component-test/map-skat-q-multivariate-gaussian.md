# SKAT statistics of Gaussian phenotypes with mean X α are χ² mixtures

Let `X` be a real `n × q` covariate matrix and `V` a real `n × n` matrix such that `Xᵀ V⁻¹ X` is
invertible, where the inverse of a singular matrix is taken to be `0`. Let `G` be a real `n × m`
genotype matrix, `w` real weights, `α ∈ ℝ^q` and `V'` a real `n × n` matrix. If `y ~ N(X α, V')`, a
phenotype whose mean `X α` lies in the span of the covariates, then the [SKAT statistic](skat-q.md)
has the weighted chi-square law

`Q ~ ∑ⱼ λⱼ χ²₁`,

the law of `∑ⱼ λⱼ ξⱼ²` for independent standard normal `ξ₁, …, ξₙ`, where `λ₁, …, λₙ` are the
eigenvalues, with multiplicity, of the [mixture matrix](skat-mixture-matrix.md)
`A = (P V'^{1/2})ᵀ K (P V'^{1/2})` and `P` is the [null projection](proj-p.md) built from `V`. Here
`N(μ, S)` is the image of the standard Gaussian law on `ℝⁿ` under `z ↦ μ + S^{1/2} z`: the Gaussian
law with mean `μ` and covariance `S` when `S` is positive semidefinite, and the point mass at `μ`
otherwise, the square root of a matrix that is not positive semidefinite being taken to be `0`. For
`V'` not positive semidefinite both sides are the point mass at `0`. For a mean outside the span of
the covariates the law of `Q` need not be this mixture.

Taking `V' = V` gives the null law and `V' = V + τ K` the law under the variance-component
alternative; both are covariances when `V` is positive semidefinite, `τ ≥ 0` and `w ≥ 0`.
