# Rational incidence matrix of a network

For finitely many buses and branches, each branch with a tail and a head bus, the rational incidence
matrix has entry `[v = tail(e)] - [v = head(e)]` at bus `v` and branch `e` (`1` at the tail, `-1` at
the head, `0` for a loop). The rational linear program that the exact checker assembles from such
data casts to the real one built from the cast data: [matrix](rat-lp-matrix-map.md),
[right-hand side](cast-vec-rat-lp-rhs.md), [objective](cast-vec-rat-lp-objective.md) and
[encoded point](cast-vec-rat-encode.md).
