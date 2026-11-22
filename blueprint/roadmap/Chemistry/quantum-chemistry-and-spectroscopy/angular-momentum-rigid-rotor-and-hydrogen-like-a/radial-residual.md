# Radial Schrödinger operator for hydrogen-like atoms

Radial residual of a hydrogen-like atom in atomic units, for nuclear charge `Z`, orbital quantum
number `l` and values `R`, `R'`, `R''` of a radial function and its first two derivatives at the
radius `r`: `-1/2 * R'' - (1/r) * R' + (l*(l+1)/(2*r^2) - Z/r) * R`. The radial equation with energy
`E` says that the residual equals `E * R`. At `r = 0` the terms with `1/r` and `1/r^2` are `0`, by
the convention `x / 0 = 0`.
