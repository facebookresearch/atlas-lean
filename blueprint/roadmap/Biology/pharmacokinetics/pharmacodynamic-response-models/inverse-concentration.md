# Concentration giving a prescribed response

For a baseline `E0`, a maximal increment `Emax`, a half-saturation concentration `K`, a Hill
coefficient `h` and a response value `E`, all real, the inverse concentration is
`K * ((E - E0) / (E0 + Emax - E)) ^ (1 / h)` (real power). It is defined for all real inputs, with
the conventions `x / 0 = 0`, `x ^ 0 = 1`, `0 ^ t = 0` for `t ≠ 0` and `x ^ t = |x| ^ t * cos (π t)`
for `x < 0`: it is `K` when `h = 0`, where the exponent `1 / h` is `0`; for `h ≠ 0` it is `0` at
`E = E0` and at `E = E0 + Emax`; and a response value outside the closed interval between `E0` and
`E0 + Emax` gives a negative base. The intended domain is `K > 0`, `h > 0`, `Emax > 0` and
`E0 < E < E0 + Emax`, where it is the concentration at which the
[response attains `E`](response-inverse-concentration.md).
