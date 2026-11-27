# Every C² solution of M x″ + K x = 0 is the modal response

Let `n` be a finite set, `M`, `K` and `C` real `n × n` matrices and `μ : n → ℝ` with `Cᵀ M C = 1`,
`Cᵀ K C = diag(μ)` and `μ_i ≥ 0` for every `i`. If `x : ℝ → ℝⁿ` is twice continuously
differentiable with `M x''(t) + K x(t) = 0` at every time `t`, then `x` is the
[modal response](modal-response.md) with its own initial data `x(0)` and `x'(0)`. In particular
the response does not depend on the choice of `C` within these conditions.
