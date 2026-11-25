# Rational constraint matrix of the dispatch linear program

For the rational data of a dispatch problem, the rational LP matrix is `[F, -F]`, with `F` the
[rational constraint matrix on generation and angles](rat-free-constraint-matrix.md) acting on the
positive parts and `-F` on the negative parts. Its entries are given by the same formula as for the
real linear program, over the rationals, so that the checker is an exact finite test. The cast of
the assembled rational program is the real one: [matrix](rat-lp-matrix-map.md),
[right-hand side](cast-vec-rat-lp-rhs.md), [objective](cast-vec-rat-lp-objective.md) and
[encoded point](cast-vec-rat-encode.md).
