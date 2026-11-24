# Gradient of the conductive geotherm with heat production

For a layer of thickness `L`, conductivity `k`, uniform heat production `H`, surface temperature
`Ts` and basal temperature `Tb`, the conductive geotherm
`T(d) = Ts + [(Tb - Ts) / L + H * L / (2 * k)] * d - H * d ^ 2 / (2 * k)` has derivative
`(Tb - Ts) / L + H * L / (2 * k) - H * d / k` at every depth `d`. This holds for all real
parameters, with the convention `x / 0 = 0`: the quotients by `L` are `0` when `L = 0`, and those
by `k` are `0` when `k = 0`. The intended domain is `L > 0` and `k > 0`.
