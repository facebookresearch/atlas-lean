# Atmosphere–ocean–land total carbon changes only by external fluxes

The carbon contents `Catm`, `Cocean` and `Cland` of the atmosphere, ocean and land exchange the
real fluxes `Fao` (atmosphere to ocean), `Foa` (ocean to atmosphere), `Fal` (atmosphere to land),
`Fla` (land to atmosphere), `Fol` (ocean to land) and `Flo` (land to ocean), and receive the real
external fluxes `e_atm`, `e_ocean` and `e_land`. If at time `t` the three contents have
derivatives `(Foa - Fao) + (Fla - Fal) + e_atm`, `(Fao - Foa) + (Flo - Fol) + e_ocean` and
`(Fal - Fla) + (Fol - Flo) + e_land`, then the total `Catm + Cocean + Cland` has derivative
`e_atm + e_ocean + e_land` at `t`: the internal transfers cancel.
