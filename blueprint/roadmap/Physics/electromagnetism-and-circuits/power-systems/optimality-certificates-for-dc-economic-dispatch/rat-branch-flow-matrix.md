# Rational branch-flow coefficient matrix

For a network with rational susceptances `b`, the rational branch-flow matrix is `diag(b) Bᵀ`, with
`B` the [rational incidence matrix](rat-incidence.md). Its entries are given by the same formula as
for the real linear program, over the rationals, so that the checker is an exact finite test. The
cast of the assembled rational program is the real one: [matrix](rat-lp-matrix-map.md),
[right-hand side](cast-vec-rat-lp-rhs.md), [objective](cast-vec-rat-lp-objective.md) and
[encoded point](cast-vec-rat-encode.md).
