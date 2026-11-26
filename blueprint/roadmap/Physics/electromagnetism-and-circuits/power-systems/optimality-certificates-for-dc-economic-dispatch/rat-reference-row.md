# Rational row selecting the reference angle

For finitely many buses and a reference bus `r`, the rational reference row is the `1 × n_N` row
with entry `1` at `r` and `0` elsewhere. The rational linear program that the exact checker
assembles from such data casts to the real one built from the cast data:
[matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
