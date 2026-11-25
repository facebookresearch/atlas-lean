# Speed density of the Wright–Fisher diffusion with mutation

For real numbers `θ₁`, `θ₂` and `x`, let `m(x) = 2 x ^ (θ₁ - 1) (1 - x) ^ (θ₂ - 1)`, with real
powers. For `x ∈ (0, 1)` it equals `2 / (x (1 - x) ψ(x))` with the
[scale density with mutation](mutation-scale-density.md) `ψ`. Outside `(0, 1)` the real powers
follow the conventions `0 ^ 0 = 1`, `0 ^ t = 0` for `t ≠ 0` and `s ^ t = |s| ^ t cos (π t)` for
`s < 0`. So `m(0) = 0` if `θ₁ ≠ 1` and `m(0) = 2` if `θ₁ = 1`; `m(1) = 0` if `θ₂ ≠ 1` and
`m(1) = 2` if `θ₂ = 1`.
