# Heat load per unit area over a finite horizon

Let `C` be a [stagnation-point heating correlation](stagnation-heating-correlation.md) with
coefficient `k_SG`, let `t_f ≥ 0`, and let `ρ`, `r_n` and `v` be real functions of time whose
values lie in the validity box of `C` ([applies](applies.md)) at every `t ∈ [0, t_f]`. The heat
load of this history over `[0, t_f]` is

`∫ from 0 to t_f of k_SG √(ρ(t) / r_n(t)) v(t)³ dt`.

It is heat per unit area, `J / m²` in SI units; the heat into a surface needs a declared area to
multiply it. It is the heat load only when the flux `t ↦ k_SG √(ρ(t) / r_n(t)) v(t)³` is
integrable on `[0, t_f]`: otherwise the integral is `0` by convention.
