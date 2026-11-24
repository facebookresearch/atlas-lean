# Rational incidence matrix of a network

For finitely many buses and branches, each branch with a tail and a head bus, the rational incidence
matrix has entry `[v = tail(e)] - [v = head(e)]` at bus `v` and branch `e` (`1` at the tail, `-1` at
the head, `0` for a loop). Its entries are given by the same formula as for the real linear program,
over the rationals, so that the checker is an exact finite test. The cast of the assembled rational
program is the real one: [matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
