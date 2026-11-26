# With the endpoint fluxes swapped the energy balance fails

For the ramp `v = i = x − t` on the lossless line with `L = C = 1` and `R = G = 0`, a
[solution](ramp-wave-is-telegrapher-solution.md), on the segment `[0, 1]` over the time window
`[0, 1/2]`, the change of the [line energy](line-energy.md) is
`E(1/2) − E(0) = 1/12 − 1/3 = −1/4`, while the balance with the endpoint fluxes swapped
(outflow at `x = 0`, inflow at `x = 1`) gives

`∫ from 0 to 1/2 of (S(1, s) − S(0, s)) ds − 0 = 1/4`.

So the two differ, and the [integrated balance](line-energy-sub-eq-integral-endpoint-flu.md)
needs the inflow at `x = 0` and the outflow at `x = ℓ`.
