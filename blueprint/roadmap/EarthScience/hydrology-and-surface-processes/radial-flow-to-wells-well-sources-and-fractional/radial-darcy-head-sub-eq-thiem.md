# The radial Darcy head difference is the Thiem one at the reversed rate

Let `r0 > 0` and `Tr > 0`, and let the head `h` be continuous on `r0 ≤ r ≤ r1`, with derivative
`h'(r)` and steady outward discharge `-2 * π * r * Tr * h'(r) = Q` at every `r0 < r < r1`. Then for
every constant `C` and every `r0 ≤ r ≤ r1`,
`h(r) - h(r0) = (C + (-Q) * log r / (2 * π * Tr)) - (C + (-Q) * log r0 / (2 * π * Tr))`: the head
difference is the [Thiem head difference](../thiem-well-flow/thiem-head-difference.md) for the
pumping rate `-Q`.
