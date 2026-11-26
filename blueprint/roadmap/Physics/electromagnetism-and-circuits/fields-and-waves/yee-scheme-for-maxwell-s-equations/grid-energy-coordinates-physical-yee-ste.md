# In energy coordinates a physical Yee step is a leapfrog step

For free space with permittivity `ε₀ > 0` and permeability `μ₀ > 0`, all reals `h` and `dt` and grid
fields `E, H ∈ ℝᴺ`, the [energy coordinates](grid-energy-coordinates.md) of one
[physical Yee step](physical-yee-step.md) from `(E, H)` are one leapfrog step at the free-space
speed of light `c = 1 / √(ε₀ μ₀)` from `(u, v) = (√ε₀ E, −√μ₀ H)`: `v_new = v − c dt D₊ᵀ u` and then
`u_new = u + c dt D₊ v_new`, where `D₊` is the periodic forward difference and `D₊ᵀ` its transpose.
