# Monatomic ideal-gas entropy

Ideal-gas entropy `S = N * kB * (log (V/N) + (3/2) * log (U/N) + s0)` with a constant `kB` (the
Boltzmann constant per particle, energy per temperature per particle) and a dimensionless reference
entropy per particle `s0` (absorbing the thermal-wavelength and reference-state constants). Physical
domain: `U > 0`, `V > 0`, `N > 0`; outside it the value follows the conventions `x / 0 = 0`,
`log 0 = 0` and `log x = log |x|` for `x < 0`.
