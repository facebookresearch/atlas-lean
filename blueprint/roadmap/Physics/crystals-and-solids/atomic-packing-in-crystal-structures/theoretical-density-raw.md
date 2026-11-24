# Theoretical Density Raw

Raw density expression `n * A / (Vc * NA)`: `n` atoms per cell, molar mass
`A`, cell volume `Vc`, Avogadro constant `NA`, on arbitrary reals `A`, `Vc` and
`NA`. Lean's division is total, so this is `0` for `Vc = 0` or `NA = 0`; it is a
density only for `0 < A`, `0 < Vc` and `0 < NA`, the domain that
`theoreticalDensity` enforces.
