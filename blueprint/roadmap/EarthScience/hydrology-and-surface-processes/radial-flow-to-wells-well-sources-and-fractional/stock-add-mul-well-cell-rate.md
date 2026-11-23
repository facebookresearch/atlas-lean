# Finite-volume ledger with wells

The cell rates sum to the transport total
`totalDiscreteChange Δx F` plus the well total over `Δx`, and one explicit step
`c i ↦ c i + dt * wellCellRate Δx F q i` changes the stock `Δx * ∑ i, c i` by `dt` times the net
boundary inflow `F 0 - F (Fin.last n)` plus the well total `∑ i, q i`. The exterior fluxes may
be nonzero; the interior fluxes cancel (`totalDiscreteChange_eq`).
