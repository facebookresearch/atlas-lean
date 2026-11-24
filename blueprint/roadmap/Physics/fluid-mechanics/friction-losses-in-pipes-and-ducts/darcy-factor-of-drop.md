# Darcy Factor Of Drop

The Darcy friction factor `f = 2 D Δp / (ρ V |V| L)` of an oriented pressure drop `Δp` over a
length `L > 0` of a duct of diameter `D > 0` carrying a fluid of density `ρ > 0` at the signed
mean velocity `V`, for a drop in the direction of the flow (`0 < Δp V`): the oriented
Darcy-Weisbach relation `Δp = f (L / D) ρ V |V| / 2` of `darcyWeisbach_eq` solved for `f`.
Reversing both `V` and `Δp` keeps the factor, and the factor is positive
(`darcyFactorOfDrop_pos`), as in the positive-factor loss model of this module. The domain is
part of the definition: at zero flow, or for a duct of zero length or diameter or a fluid of zero
density, the relation does not determine `f`, and a drop against the flow (`Δp V < 0`) would
describe energy generation rather than friction; no factor is defined there. The argument
`0 < Δp V` implies `V ≠ 0`.
