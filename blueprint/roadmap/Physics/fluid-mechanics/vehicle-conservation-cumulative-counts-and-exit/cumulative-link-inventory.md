# Link count after n steps from the cumulative inflows and outflows

Let `N`, `Fin` and `Fout` be real sequences indexed by the step `j`, and `dt ≥ 0` a time step. If
the vehicle count `N` of a link evolves by `N(j + 1) = N(j) + dt (Fin(j) - Fout(j))` at every step
`j`, with inflow `Fin(j)` and outflow `Fout(j)` at the link boundaries, then after `n` steps

`N(n) = N(0) + ∑_{j < n} dt Fin(j) - ∑_{j < n} dt Fout(j)`:

the initial count plus the cumulative arrivals minus the cumulative departures, both counted from
step `0`. No first-in first-out order or delay is derived from this aggregate conservation.

Equivalently, the change of the count is the summed net inflow:
`N(n) - N(0) = ∑_{j < n} dt (Fin(j) - Fout(j))`.
