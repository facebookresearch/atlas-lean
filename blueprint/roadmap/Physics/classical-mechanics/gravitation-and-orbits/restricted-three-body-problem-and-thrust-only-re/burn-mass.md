# Mass history of the normalized burn

For a real time `t`, the mass of the vehicle in the normalized burn is `m(t) = 2 - t`: initial
mass `2` and constant propellant mass flow `1`, so the mass falls from `2` to `1` on the burn
interval `[0, 1]`. The formula is defined for every real `t`; it vanishes at the depletion time
`t = 2` and is negative after it, outside the model, which uses it on `[0, 1]`.
