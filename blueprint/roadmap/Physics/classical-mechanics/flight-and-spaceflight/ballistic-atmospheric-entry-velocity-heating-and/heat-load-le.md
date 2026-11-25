# Finite-horizon bound on the heat load

Let `C` be a [stagnation-point heating correlation](stagnation-heating-correlation.md) with
coefficient `k_SG` and box limits `ρ_max`, `r_min`, `v_max`, let `t_f ≥ 0`, and let `ρ`, `r_n`,
`v` be real functions of time whose values lie in the validity box at every `t ∈ [0, t_f]`, with
the flux `t ↦ k_SG √(ρ(t) / r_n(t)) v(t)³` integrable on `[0, t_f]`. Then the
[heat load](heat-load.md) per unit area over `[0, t_f]` is at most

`t_f k_SG √(ρ_max / r_min) v_max³`.

The bound uses the constraints `k_SG ≥ 0` and `r_min > 0` of the correlation.
