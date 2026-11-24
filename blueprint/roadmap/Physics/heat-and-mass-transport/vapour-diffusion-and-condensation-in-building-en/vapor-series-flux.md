# Vapor Series Flux

Steady vapor mass flux through layers in series from boundary
partial pressures `pin` and `pout` and layer vapor resistances
`R i`: the total pressure drop divided by the total resistance.
This is the totalized quotient: it is the physical steady flux
only when the total resistance is nonzero (in particular for
positive resistances); at zero total resistance Lean's division
gives `0`, which has no physical steady-state meaning. Vapor
mass flux and partial pressure keep their own dimensions; no
heat-flux formula is asserted.
