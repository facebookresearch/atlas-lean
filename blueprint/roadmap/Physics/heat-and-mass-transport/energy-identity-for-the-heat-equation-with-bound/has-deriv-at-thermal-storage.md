# Has Deriv At thermal Storage

Storage balance at time `t`: if `dT i` is the derivative of `T i` at `t`, the conductances
are symmetric and every node obeys `C i * dT i = ∑ j, G i j * (T j t - T i t) + Q i` at `t`, the
stored heat `∑ i, C i * T i` has derivative `∑ i, Q i` at `t`: conduction between nodes cancels.
This is `ZoneHeatInventory.heat_inventory_hasDerivAt` with inputs `Q` and no heating power.
