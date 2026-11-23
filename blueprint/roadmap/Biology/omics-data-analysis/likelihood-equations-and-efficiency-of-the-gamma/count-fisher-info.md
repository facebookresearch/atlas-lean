# Count Fisher Info

The Fisher information matrix of one count at size factor `σ` and hyperparameter `(a, b)`,
`[[τ, -σ / (b (b + σ))], [-σ / (b (b + σ)), a σ / (b² (b + σ))]]`, as an operator, with the shape
entry `τ = E[∑_{j<K} 1 / (a + j)²]` (an expected trigamma increment, which has no closed form)
supplied as a parameter. `integral_countHessian`: it is minus the expected score derivative.
