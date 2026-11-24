# With zero supply and loss on an interval the storage is constant

For a [network plant](network-plant.md) with `R_e ≥ 0` on resistor branches, `L_e > 0` on inductor
branches and `C_e > 0` on capacitor branches, reals `a ≤ b`, and a [trajectory](network-trajectory.md)
that [obeys the laws on `[a, b]`](is-network-trajectory-on.md), with [supply rate](plant-supply-rate.md)
and [loss rate](plant-loss-rate.md) equal to `0` at every time of `[a, b]` and their difference
integrable on `[a, b]`, the [storage](plant-storage.md) at every `t ∈ [a, b]` equals its value at `a`.
