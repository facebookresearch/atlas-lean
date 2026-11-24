# Vehicle accounting as the total discrete balance of face fluxes

With the cells, fluxes, time step `dt` and cell width `dx > 0` of the
[conservative update](total-vehicle-change.md) `k_i' = k_i + (dt / dx) (F_i - F_{i+1})`, the total
vehicle change is `∑_{i < n} dx (k_i' - k_i) = dx dt ∑_{i < n} (F_i - F_{i+1}) / dx`: `dx dt` times
the total discrete balance of the face fluxes, the inflow minus the outflow per unit width summed
over the cells.
