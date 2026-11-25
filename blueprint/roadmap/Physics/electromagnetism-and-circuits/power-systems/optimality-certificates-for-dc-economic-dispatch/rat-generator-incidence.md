# Rational generator-to-bus incidence matrix

For finitely many buses and generators placed at buses, the rational generator incidence has entry
`1` at bus `v` and generator `g` when `g` is at `v`, and `0` otherwise. The rational linear program
that the exact checker assembles from such data casts to the real one built from the cast data:
[matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
