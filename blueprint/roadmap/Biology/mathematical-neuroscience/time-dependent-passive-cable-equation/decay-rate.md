# Decay rate of a sealed-end mode

For real numbers `τ`, `ℓ` and `L` and a natural number `n`, the rate of the `n`-th sealed-end mode
of the cable equation `τ ∂ₜV = ℓ² ∂ₓ²V - V` on `[0, L]` is

`k_n = (1 + ℓ² (n π / L)²) / τ`.

For `τ ≠ 0` the separated solution `e^(-k_n t) cos (n π x / L)` solves the cable equation
([finite expansions](is-cable-solution-cable-sum.md)). For `τ > 0`, `k_n > 0`
([positivity](decay-rate-pos.md)) is a decay rate and `1 / k_n` is Rall's `n`-th equalizing time
constant. The formula is defined for all real inputs: with the convention `u / 0 = 0`, `k_n = 0`
for every `n` when `τ = 0`, and `k_n = 1 / τ` for every `n` when `L = 0`. In the model `τ`, `ℓ`
and `L` are positive.
