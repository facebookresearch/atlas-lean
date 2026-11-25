# The logarithmic head profile carries the prescribed discharge

For a well radius `r0 > 0`, a transmissivity `Tr > 0`, a well head `h0` and any discharge `Q`, the
[radial Darcy head](radial-darcy-head.md) `h(r) = h0 - Q * log (r / r0) / (2 * π * Tr)` has
derivative `h'(r) = -Q / (2 * π * Tr * r)` at every radius `r > 0`, and its outward discharge
`-2 * π * r * Tr * h'(r)` there is `Q`.
