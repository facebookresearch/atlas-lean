# Jacobian matrix of the toggle switch

For reals `α₁, α₂`, `β, γ ∈ ℕ` and reals `u, v`, the real `2 × 2` matrix
`[[−1, h₁'(v)], [h₂'(u), −1]]`, where `h₁'(v) = −α₁ β v^{β−1} / (1 + v^β)²` and
`h₂'(u) = −α₂ γ u^{γ−1} / (1 + u^γ)²` are the [derivative of the Hill repression](hill-deriv.md)
functions, with the conventions stated there. The formula is defined for all real `(u, v)`; for
`u, v ≥ 0` its entries are the partial derivatives of the right-hand sides of the toggle switch
`u' = α₁ / (1 + v^β) − u`, `v' = α₂ / (1 + u^γ) − v`.
