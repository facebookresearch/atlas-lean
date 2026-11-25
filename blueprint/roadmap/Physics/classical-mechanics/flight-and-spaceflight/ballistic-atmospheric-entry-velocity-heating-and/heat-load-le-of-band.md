# Heat-load bound along the profile in an altitude band below entry

Let `C` be a [stagnation-point heating correlation](stagnation-heating-correlation.md) with
coefficient `k_SG` and smallest nose radius `r_min`. Let `ρ₀ > 0`, `H > 0`, `β > 0`,
`sin γ > 0` (a downward path) and `v_e > 0`, let `h_e`, `h_min` be real and `t_f ≥ 0`. Let `h`
and `r_n` be real functions of time with `h_min ≤ h(t) ≤ h_e` for every `t ∈ [0, t_f]`, such that
the history `(ρ(h(t)), r_n(t), v(h(t)))` lies in the validity box of `C` at every `t ∈ [0, t_f]`
and its flux `t ↦ k_SG √(ρ(h(t)) / r_n(t)) v(h(t))³` is integrable on `[0, t_f]`, where
`ρ(z) = ρ₀ exp(−z / H)` is the [exponential density](exponential-density.md) and `v` the
[finite-entry ballistic velocity profile](ballistic-velocity.md) with entry state `(h_e, v_e)`.
Then the [heat load](heat-load.md) per unit area of this history over `[0, t_f]` is at most

`t_f k_SG √(ρ(h_min) / r_min) v_e³`:

in the band the density is at most `ρ(h_min)` and the speed at most `v_e`, and the bound uses the
constraints `k_SG ≥ 0` and `r_min > 0` of the correlation.
