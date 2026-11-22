# Monatomic ideal-gas entropy

Ideal-gas entropy (MOD): `S = N * kB * (log (V/N) + (3/2) * log (U/N) + s0)`
with a symbolic constant `kB` (per-particle Boltzmann constant, energy per
temperature per particle; positive in the lemmas that need it) and dimensionless
reference entropy per particle `s0` (absorbing the thermal-wavelength and
reference-state constants). Physical domain: `U > 0`, `V > 0`, `N > 0`; outside it
the value is junk fixed by Lean's conventions (`Real.log` of a nonpositive argument,
division by zero).
