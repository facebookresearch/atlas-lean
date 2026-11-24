# Stochastic mass-action system of the SEIR network

For nonnegative `β`, `σ`, `γ`, `μ` and a system size `N ∈ ℕ`: the stochastic reaction network on the
[SEIR reaction network](network.md) with the mass-action propensities at system size `N`. Reaction
`c` has, in the state `z ∈ ℕ^{S, E, I, R}`, the propensity

`λ^N_c(z) = N κ_c ∏_X ((z_X)_(k_X) / N^(k_X))`,

where `κ = (μ, β, σ, γ, μ, μ, μ, μ)` are the [rate constants](rate-const.md), `k` is the
[reactant complex](network-src.md) of `c`, and `(n)_(k) = n (n - 1) ⋯ (n - k + 1)` is the falling
factorial (`1` for `k = 0`, `0` for `n < k`). The rate constants are nonnegative, so the
propensities are nonnegative, and a propensity vanishes when some count is below its reactant
coefficient. At `N = 0` division by zero gives `0`, and every propensity is `0`; the intended domain
is `N ≥ 1`. On this network `λ^N_c(z) = N λ_c(z / N)` with `λ_c` the
[scaled intensity](scaled-rate.md) ([propensities](propensity-chain-crn.md)).
