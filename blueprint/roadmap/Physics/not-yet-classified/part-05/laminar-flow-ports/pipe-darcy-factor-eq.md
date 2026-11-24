# Laminar Darcy factor

For `ρ, μ, R, L > 0` (positive density, viscosity, radius and
length) and `G ≠ 0` (a nonzero flow, in either direction), the Darcy factor
(`FluidDynamics.PipeFrictionPorts.darcyFactorOfDrop`) of the oriented Poiseuille pressure drop
`G L` over the length `L` on the diameter `D = 2 R` at the signed mean velocity `V` is `64 / Re`,
with `Re = ρ |V| D / μ`.
