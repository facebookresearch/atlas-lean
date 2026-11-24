# Change of the link count after n steps is the summed net inflow

Let `N`, `Fin` and `Fout` be real sequences indexed by the step `j`, and `dt ≥ 0` a time step. If
`N(j + 1) = N(j) + dt (Fin(j) - Fout(j))` at every step `j`, then after `n` steps
`N(n) - N(0) = ∑_{j < n} dt (Fin(j) - Fout(j))`, the summed net inflow; this is the
[cumulative inventory](cumulative-link-inventory.md) with arrivals and departures combined.
