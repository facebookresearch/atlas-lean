# Drag deceleration along the ballistic profile

For real numbers `ρ₀`, `H`, `β`, `γ`, `h_e`, `v_e` and `h`, the drag deceleration along the
finite-entry profile is

`a(h) = ρ(h) v(h)² / (2 β)`,

with `ρ(h) = ρ₀ exp(−h / H)` the [exponential density](exponential-density.md) and `v` the
[finite-entry ballistic velocity profile](ballistic-velocity.md) with entry state `(h_e, v_e)`.
For `ρ₀ ≥ 0` and `β > 0` it is the magnitude of the drag term `v' = −ρ(h) v² / (2 β)` at the
altitude `h`. With the convention `x / 0 = 0`, `a` is identically `0` when `β = 0`.
