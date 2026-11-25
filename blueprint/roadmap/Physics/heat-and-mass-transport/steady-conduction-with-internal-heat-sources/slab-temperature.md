# Temperature of a steady slab with a uniform heat source

For real `Ts`, `Tb`, `L`, `k`, `H` and `d`, the slab temperature is

`T(d) = Ts + ((Tb - Ts)/L + HL/(2k)) d - H d²/(2k)`,

the profile of a slab of thickness `L` and conductivity `k` with surface temperatures `Ts` and `Tb`
and a uniform volumetric heat source `H`: it [equals `Ts` at `d = 0`](slab-temperature-zero.md), for
`L, k ≠ 0` it [equals `Tb` at `d = L`](slab-temperature-length.md), and for `k > 0` it satisfies the
[steady heat equation](../../../EarthScience/solid-earth-geophysics/conductive-geotherms/geotherm-second-deriv.md)
`k T″ + H = 0`. It is intended for `L ≠ 0` and `k ≠ 0`; with `x/0 = 0` the term `(Tb - Ts)/L` is `0`
when `L = 0` and the terms divided by `k` are `0` when `k = 0`. In the physical reading `L > 0`,
`k > 0` and `0 ≤ d ≤ L`.
