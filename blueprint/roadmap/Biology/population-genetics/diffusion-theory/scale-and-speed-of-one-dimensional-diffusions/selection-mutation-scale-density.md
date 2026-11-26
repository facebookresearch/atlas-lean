# Scale density with selection and mutation

For real numbers `α`, `θ₁`, `θ₂` and `x`, let

`ψ(x) = e^(-2αx) x ^ (-θ₁) (1 - x) ^ (-θ₂)`,

with real powers. For `x ∈ (0, 1)` it is [positive](selection-mutation-scale-density-pos.md) and
[solves](has-deriv-at-selection-mutation-scale-de.md) `ψ' = -(2b/a) ψ` for the variance
`a(x) = x (1 - x)` and the drift `b(x) = α x (1 - x) + (θ₁ (1 - x) - θ₂ x) / 2` of the
Wright–Fisher diffusion with genic selection and two-way mutation. Outside `(0, 1)` the real
powers follow the conventions `0 ^ 0 = 1`, `0 ^ t = 0` for `t ≠ 0` and
`s ^ t = |s| ^ t cos (π t)` for `s < 0`.
