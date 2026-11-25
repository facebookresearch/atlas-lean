# Logarithmic radial Darcy head profile

For a head `h0` at the well radius `r0`, a constant outward discharge `Q` and a transmissivity
`Tr`, the radial Darcy head at radius `r` is `h(r) = h0 - Q * log (r / r0) / (2 * π * Tr)`. It is
defined for all real arguments, with the conventions `x / 0 = 0` and `log x = log |x|` (so
`log 0 = 0`): it is `h0` when `r = 0`, `r0 = 0` or `Tr = 0`. The intended domain is `Tr > 0` and
`0 < r0 ≤ r`, where it [carries the outward discharge `Q`](radial-darcy-head-solves.md).
