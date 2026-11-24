# Mass-action propensities equal the chain's intensities

Let `β`, `σ`, `γ`, `μ` be nonnegative. For every `N ∈ ℕ`, [channel](channel.md) `c` and count vector
`z ∈ ℕ^{S, E, I, R}`, the propensity of reaction `c` in the
[stochastic mass-action system](chain-crn.md) at system size `N` is exactly

`λ^N_c(z) = N λ_c(z_S / N, z_E / N, z_I / N, z_R / N)`,

with `λ_c` the [scaled intensity](scaled-rate.md). For `N ≥ 1` these are `μ N`, `β z_S z_I / N`,
`σ z_E`, `γ z_I`, `μ z_S`, `μ z_E`, `μ z_I` and `μ z_R`; at `N = 0`, where division by zero gives
`0`, both sides are `0`.
