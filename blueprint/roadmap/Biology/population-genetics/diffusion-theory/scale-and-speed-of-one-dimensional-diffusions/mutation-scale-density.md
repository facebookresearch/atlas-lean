# Scale density of the Wright–Fisher diffusion with mutation

For real numbers `θ₁`, `θ₂` and `x`, let `ψ(x) = x ^ (-θ₁) (1 - x) ^ (-θ₂)`, with real powers. For
`x ∈ (0, 1)` it is positive and finite for all real `θ₁`, `θ₂`; there it is, up to a positive
constant factor, the [scale density](../selection-duality-and-general-one-dimensional-di/scale-density.md) of the Wright–Fisher diffusion with
variance `x (1 - x)` and mutation drift `(θ₁ (1 - x) - θ₂ x) / 2`. Outside `(0, 1)` the real
powers follow the conventions `0 ^ 0 = 1`, `0 ^ t = 0` for `t ≠ 0` and
`s ^ t = |s| ^ t cos (π t)` for `s < 0`. So `ψ(0) = 0` if `θ₁ ≠ 0` and `ψ(0) = 1` if `θ₁ = 0`;
`ψ(1) = 0` if `θ₂ ≠ 0` and `ψ(1) = 1` if `θ₂ = 0`.
