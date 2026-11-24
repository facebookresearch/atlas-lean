# The heat flux is bounded by its value at the corner of the box

For a [stagnation-point heating correlation](stagnation-heating-correlation.md) with coefficient
`k_SG` and box limits `ρ_max`, `r_min`, `v_max`, at every point `(ρ, r_n, v)` where it
[applies](applies.md) the [heat flux](heat-flux.md) satisfies

`k_SG √(ρ / r_n) v³ ≤ k_SG √(ρ_max / r_min) v_max³`.

The bound uses the constraints `k_SG ≥ 0` and `r_min > 0` of the correlation.
