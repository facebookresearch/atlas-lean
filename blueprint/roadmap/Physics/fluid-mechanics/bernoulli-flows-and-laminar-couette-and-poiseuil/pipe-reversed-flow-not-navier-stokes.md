# Pipe Reversed Flow not navier Stokes

Reversing the pressure gradient without reversing the flow fails the momentum balance: for
`μ ≠ 0` and `G ≠ 0` the Poiseuille velocity with the pressure `p₀ + G z` does not satisfy
Physlib's Navier-Stokes equations; its axial momentum residual is `-2 G`.
