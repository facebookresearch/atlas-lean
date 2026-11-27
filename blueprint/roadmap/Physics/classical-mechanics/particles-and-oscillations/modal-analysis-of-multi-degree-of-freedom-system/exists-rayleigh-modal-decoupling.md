# Modal basis for Rayleigh damping with nonnegative modal coefficients

Let `n` be a finite set, `M` a positive-definite and `K` a positive-semidefinite real `n × n`
matrix, and `α ≥ 0`, `β ≥ 0`. Then there are an invertible real `n × n` matrix `Φ` and
`μ : n → ℝ` with `Φᵀ M Φ = 1`, `Φᵀ K Φ = diag(μ)`, `μ_j ≥ 0` and `α + β μ_j ≥ 0` for every `j`,
such that for all `x, f : ℝ → ℝⁿ` and every time `t`,

`M x''(t) + (α M + β K) x'(t) + K x(t) = f(t)`

holds if and only if `(q'')_j(t) + (α + β μ_j) (q')_j(t) + μ_j q_j(t) = (Φᵀ f(t))_j` for every
`j`, with `q = Φᵀ M x` ([decoupling](rayleigh-modal-decoupling.md)). Derivatives take the value `0`
where the function is not differentiable, and `(q')_j`, `(q'')_j` are the `j`-th components of the
derivatives of the vector `q`. Repeated eigenvalues and rigid modes (`μ_j = 0`) are
included.
