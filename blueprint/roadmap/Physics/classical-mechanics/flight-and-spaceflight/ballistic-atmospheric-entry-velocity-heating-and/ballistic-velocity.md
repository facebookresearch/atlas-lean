# Finite-entry ballistic velocity profile

For real numbers `ρ₀`, `H`, `β`, `γ`, the entry altitude `h_e`, the entry speed `v_e` and the
altitude `h`, the finite-entry ballistic velocity profile is

`v(h) = v_e exp(K (exp(−h_e / H) − exp(−h / H)))`,

with `K = ρ₀ H / (2 β sin γ)` the [ballistic entry constant](ballistic-k.md). It is the speed of a
drag-dominated vehicle entering an [exponential atmosphere](exponential-density.md) at altitude
`h_e` with speed `v_e` along a straight path at the downward angle `γ`, gravity and lift
neglected. In the physical reading `ρ₀, H, β, v_e > 0` and `sin γ > 0`. With the convention
`x / 0 = 0`, the profile is the constant `v_e` when `H = 0` or `β sin γ = 0`.
