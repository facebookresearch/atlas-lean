# Along altitude trajectories the profile speed solves the drag equation

Let `H ≠ 0`, `β > 0` and `sin γ > 0`, a downward path, and let `ρ₀`, `h_e`, `v_e` and `t` be
real. Write `v` for the [finite-entry ballistic velocity profile](ballistic-velocity.md) and
`ρ(z) = ρ₀ exp(−z / H)` for the [exponential density](exponential-density.md). If an altitude
trajectory `h` has the derivative `h'(t) = −v(h(t)) sin γ` at `t`, then the speed `τ ↦ v(h(τ))`
has at `t` the derivative

`−ρ(h(t)) v(h(t))² / (2 β)`,

so it satisfies the drag equation `v' = −ρ(h) v² / (2 β)` at `t`. This is the converse of
[the derivation of the profile](ballistic-velocity-of-ode.md) from the equations of motion.
