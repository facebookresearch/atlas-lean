# CFL number of the normalized upwind update

For a total volumetric rate `Q`, a time step `dt`, a porosity `φ`, a cross-section `A`, a cell
length `dx` and a mobile saturation range `ΔS`, the CFL number of the normalized update is
`ν = Q * dt / (φ * A * dx * ΔS)`. It is defined for all real arguments: with the convention
`x / 0 = 0` it is `0` when `φ * A * dx * ΔS = 0`. The intended domain is a positive pore volume
`φ * A * dx > 0`, `ΔS > 0`, `Q ≥ 0` and `dt ≥ 0`.
