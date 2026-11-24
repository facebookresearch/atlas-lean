# Finite-horizon passivity when the network laws hold on an interval

For a [network plant](network-plant.md) with `R_e ≥ 0` on resistor branches, `L_e > 0` on inductor
branches and `C_e > 0` on capacitor branches, reals `a ≤ b`, and a [trajectory](network-trajectory.md)
that [obeys the laws on `[a, b]`](is-network-trajectory-on.md), with continuous
[supply rate](plant-supply-rate.md) on `[a, b]` and with supply rate minus
[loss rate](plant-loss-rate.md) integrable on `[a, b]`, the trajectory is
[finite-horizon passive on `[a, b]`](finite-horizon-passive-on.md): `E(b) - E(a) ≤ ∫_a^b s(t) dt`.
