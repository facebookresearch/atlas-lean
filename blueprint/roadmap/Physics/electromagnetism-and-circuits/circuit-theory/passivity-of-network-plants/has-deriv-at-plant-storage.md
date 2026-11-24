# At interior times the storage changes at supply minus loss

For a [network plant](network-plant.md) with `R_e ≥ 0` on resistor branches, `L_e > 0` on inductor
branches and `C_e > 0` on capacitor branches, reals `a` and `b`, a [trajectory](network-trajectory.md)
that [obeys the laws on `[a, b]`](is-network-trajectory-on.md) and a time `t ∈ (a, b)`, the
[storage](plant-storage.md) has derivative `s(t) - ℓ(t)` at `t`, where `s` is the
[supply rate](plant-supply-rate.md) and `ℓ` the [loss rate](plant-loss-rate.md).
