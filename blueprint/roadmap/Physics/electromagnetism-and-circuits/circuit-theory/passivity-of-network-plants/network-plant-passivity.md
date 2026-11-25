# Passivity of a network plant with passive elements

For a [network plant](network-plant.md) with `R_e ≥ 0` on resistor branches, `L_e > 0` on inductor
branches and `C_e > 0` on capacitor branches:

- along every [trajectory](network-trajectory.md) and at every time, the [storage](plant-storage.md)
  is nonnegative;
- along every trajectory that [obeys the laws at every time](is-network-trajectory.md), the
  derivative of the storage at every time is the [supply rate](plant-supply-rate.md) minus the
  [loss rate](plant-loss-rate.md);
- the plant is [finite-horizon passive](is-finite-horizon-passive.md).
