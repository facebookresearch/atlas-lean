# The radiosity equations give the parallel-plate exchange formula

Let the emissivities of two plates satisfy `0 < ε_i ≤ 1`, let `A` and `σ` be real numbers, and let
`J` solve the [radiosity equations](is-radiosity.md) for `σ`, `ε` and temperatures `T` with the
[parallel-plate view factors](parallel-plate-view-factor.md). Then the
[gray net power](gray-net-power.md) leaving plate `0`, both plates having area `A`, is

`σ A (T₀⁴ - T₁⁴) / (1/ε₀ + 1/ε₁ - 1)`,

the [parallel-plate power](parallel-plate-power.md). The identity is exact for the infinite-plane
idealization; for finite plates it is an approximation.
