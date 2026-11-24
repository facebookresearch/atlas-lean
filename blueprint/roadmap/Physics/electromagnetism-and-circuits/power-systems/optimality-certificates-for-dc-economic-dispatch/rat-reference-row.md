# Rational row selecting the reference angle

For finitely many buses and a reference bus `r`, the rational reference row is the `1 × n_N` row
with entry `1` at `r` and `0` elsewhere. Its entries are given by the same formula as for the real
linear program, over the rationals, so that the checker is an exact finite test. The cast of the
assembled rational program is the real one: [matrix](rat-lp-matrix-map.md),
[right-hand side](cast-vec-rat-lp-rhs.md), [objective](cast-vec-rat-lp-objective.md) and
[encoded point](cast-vec-rat-encode.md).
