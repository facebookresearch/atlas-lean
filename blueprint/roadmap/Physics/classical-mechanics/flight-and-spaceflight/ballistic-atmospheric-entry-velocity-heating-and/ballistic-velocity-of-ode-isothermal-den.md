# In an isothermal layer the entry speed follows the ballistic profile

Let `g > 0`, `R_s > 0`, `T > 0`, `β > 0` and `sin γ > 0` (a downward path), let `ρ₀`, `h_e`,
`v_e`, `z₁` and `z₂` be real, and let `t₀ ≤ t₁`. Let `h` and `v` be real functions of time such
that on `[t₀, t₁]` the altitude stays in the band, `z₁ ≤ h(t) ≤ z₂`, and

`h'(t) = −v(t) sin γ` and `v'(t) = −ρ_iso(h(t)) v(t)² / (2 β)`,

where `ρ_iso` is the [isothermal-layer density](../aircraft-performance-drag-polar-power-required-a/isothermal-density.md)
with reference density `ρ₀`, gravity `g`, specific gas constant `R_s` and temperature `T`, and
with entry state `h(t₀) = h_e`, `v(t₀) = v_e`. Then for every `t ∈ [t₀, t₁]`

`v(t) = v_e exp(K (exp(−h_e / H) − exp(−h(t) / H)))`, `K = ρ₀ H / (2 β sin γ)`,

the [finite-entry ballistic velocity profile](ballistic-velocity.md) at `h(t)`, with `H` the
[scale height](../aircraft-performance-drag-polar-power-required-a/scale-height.md)
`R_s T / |g|`. The band restricts the statement to the altitudes where the isothermal layer
model holds.
