# Linearization bound

Let `f` have derivative `f'` on `[β₀ - δ, β₀ + δ]` with
`|f'(β) + D| ≤ ε D` there (`D > 0`, `0 ≤ ε < 1`): the slope stays within a factor `1 ± ε` of
`-D`. If `b` lies in that interval and `f b = 0`, then the one-step linearization
`D (b - β₀) ≈ f β₀` holds with relative error `ε / (1 - ε)`:
`|D (b - β₀) - f β₀| ≤ ε / (1 - ε) · |f β₀|`.
