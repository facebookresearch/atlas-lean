# Slab Temperature

Temperature profile of the steady one-dimensional slab with constant
conductivity and uniform volumetric heat source `H`: on a slab of
thickness `L` with surface temperatures `Ts` and `Tb`,
`T(d) = Ts + ((Tb - Ts) / L + H * L / (2k)) * d - H * d^2 / (2k)`. This is
the existing geotherm profile shape read as a slab model; `H` is an
externally supplied heat source. It is intended for `L ≠ 0`, `k ≠ 0`.
