# Along a network trajectory the storage changes at supply minus loss

For a [network plant](network-plant.md) with `R_e ≥ 0` on resistor branches, `L_e > 0` on inductor
branches and `C_e > 0` on capacitor branches, a [trajectory](network-trajectory.md) that
[obeys its laws at every time](is-network-trajectory.md), and every time `t`, the derivative of the
[storage](plant-storage.md) at `t` is `s(t) - ℓ(t)`, with `s` the [supply rate](plant-supply-rate.md)
and `ℓ` the [loss rate](plant-loss-rate.md).
