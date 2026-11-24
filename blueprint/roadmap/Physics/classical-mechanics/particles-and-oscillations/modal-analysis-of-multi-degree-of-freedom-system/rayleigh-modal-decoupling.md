# Rayleigh-damped equations decouple in modal coordinates

Let `n` be a finite set, `M`, `K` and `Φ` real `n × n` matrices and `μ : n → ℝ` with
`Φᵀ M Φ = 1` and `Φᵀ K Φ = diag(μ)`, let `α` and `β` be real numbers, `x, f : ℝ → ℝⁿ` and `t` a
time. Then

`M x''(t) + (α M + β K) x'(t) + K x(t) = f(t)`

holds if and only if, for every mode `j`, the modal coordinates `q = Φᵀ M x` satisfy

`q_j''(t) + (α + β μ_j) q_j'(t) + μ_j q_j(t) = (Φᵀ f(t))_j`.

Here `x'`, `x''`, `q'` and `q''` are first and second derivatives, with the convention that a
derivative is `0` where the function is not differentiable; no regularity of `x` is needed, and
the physical reading is the classical one for a twice differentiable `x`.
