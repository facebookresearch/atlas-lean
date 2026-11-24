# Rational generator-to-bus incidence matrix

For finitely many buses and generators placed at buses, the rational generator incidence has entry
`1` at bus `v` and generator `g` when `g` is at `v`, and `0` otherwise. Its entries are given by the
same formula as for the real linear program, over the rationals, so that the checker is an exact
finite test. The cast of the assembled rational program is the real one:
[matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
