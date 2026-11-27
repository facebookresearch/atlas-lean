# Rayleigh-damped equations decouple in modal coordinates

Let `n` be a finite set, `M`, `K` and `Φ` real `n × n` matrices and `μ : n → ℝ` with
`Φᵀ M Φ = 1` and `Φᵀ K Φ = diag(μ)`, let `α` and `β` be real numbers, `x, f : ℝ → ℝⁿ` and `t` a
time. Then

`M x''(t) + (α M + β K) x'(t) + K x(t) = f(t)`

holds if and only if, for every mode `j`, the modal coordinates `q = Φᵀ M x` satisfy

`(q'')_j(t) + (α + β μ_j) (q')_j(t) + μ_j q_j(t) = (Φᵀ f(t))_j`.

Here `x'`, `x''`, `q'` and `q''` are first and second derivatives of the vector functions, with the
convention that a derivative is `0` where the function is not differentiable, and `(q')_j`,
`(q'')_j` are the `j`-th components of the derivatives of the vector `q`; with this reading no
regularity of `x` is needed. The physical reading is the classical one for a twice differentiable
`x`, where `(q')_j` and `(q'')_j` are the derivatives of `q_j`.
