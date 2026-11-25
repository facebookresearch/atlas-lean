# Solutions of the entry equations follow the ballistic profile

Let `H ≠ 0`, `β > 0` and `sin γ > 0`, a downward path, let `ρ₀`, `h_e` and `v_e` be real, and let
`t₀ ≤ t₁`. Let `h` and `v` be real functions of time such that at every `t ∈ [t₀, t₁]`

`h'(t) = −v(t) sin γ` and `v'(t) = −ρ(h(t)) v(t)² / (2 β)`,

with `ρ(z) = ρ₀ exp(−z / H)` the [exponential density](exponential-density.md), and with entry
state `h(t₀) = h_e` and `v(t₀) = v_e`. Then for every `t ∈ [t₀, t₁]`

`v(t) = v_e exp(K (exp(−h_e / H) − exp(−h(t) / H)))`,

the [finite-entry ballistic velocity profile](ballistic-velocity.md) at the altitude `h(t)`, with
`K = ρ₀ H / (2 β sin γ)`. The equations of motion are those of a drag-dominated straight entry,
gravity and lift neglected, assumed only on the nonempty window `[t₀, t₁]`.
