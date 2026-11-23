# Well and boundary sources in the energy ledger

On a chain of `n` cells of common
positive volume `Δx`, with signed face mass fluxes `Fm` (one per face, shared by the mass and the
energy ledger) and positive face densities `ρf`, injection rates `qI` at specific enthalpies `hI`
and production rates `qP`: if each cell stores the fluid mass `m i = φ i * ρc i` (porosity
`φ i > 0`, fluid density `ρc i > 0`) and the fluid energy `E i = m i * ec i`, one explicit step of
the stored mass and energy changes the total mass by `dt ((Fm 0 - Fm n) + ∑ (qI - qP))` and the
total energy by `dt` times the net boundary enthalpy inflow plus `∑ (qI hI - qP h)`, where the
produced enthalpy `h = (E i + φ i * pc i) / m i` is that of the stored cell state. The face states
are free: the identity holds for every choice.
