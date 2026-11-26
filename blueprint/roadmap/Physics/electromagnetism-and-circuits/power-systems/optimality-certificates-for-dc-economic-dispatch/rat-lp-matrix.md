# Rational constraint matrix of the dispatch linear program

For the rational data of a dispatch problem, the rational LP matrix is `[F, -F]`, with `F` the
[rational constraint matrix on generation and angles](rat-free-constraint-matrix.md) acting on the
first nonnegative coordinate block and `-F` on the second. The rational linear program that the
exact checker assembles from such data casts to the real one built from the cast data:
[matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
