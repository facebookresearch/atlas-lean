# The box balance of `ControlVolumes`

For a fluid in a fixed box with the inlet on the face
`x₀ = a₀` and the exhaust on the face `x₀ = b₀`, both of area `A₀ = faceArea a b 0`, under the
hypotheses of `ControlVolumes.hasDerivAt_momentum_twoPort` (pressure-only uniform port data,
impermeable side walls), with a stationary momentum and no axial body force, the axial component of
the traction resultant of the side walls on the fluid is the separate-flow thrust with equal port
areas and port mass flows `ṁ = ρ A₀ v₀`, for every ambient pressure `p_a`.
