# Finite-volume ledger with wells

On a chain of `n` cells of common volume `Δx > 0`, with face fluxes `F 0, …, F n` and well rates
`q i`, let `r i = -(F (i + 1) - F i) / Δx + q i / Δx` be the [cell rates](well-cell-rate.md).
Their sum is the transport total plus the well total over `Δx`,
`∑ i, r i = ∑ i, (-(F (i + 1) - F i) / Δx) + (∑ i, q i) / Δx`. For every time step `dt` and cell
values `c i`, the explicit step `c i ↦ c i + dt * r i` changes the stock `Δx * ∑ i, c i` by `dt`
times the net boundary inflow `F 0 - F n` plus the well total:
`Δx * ∑ i, (c i + dt * r i) = Δx * ∑ i, c i + dt * ((F 0 - F n) + ∑ i, q i)`. The exterior fluxes
`F 0` and `F n` may be nonzero; the interior fluxes cancel.
