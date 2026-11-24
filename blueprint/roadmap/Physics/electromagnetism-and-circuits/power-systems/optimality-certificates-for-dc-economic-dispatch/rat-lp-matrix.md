# Rational constraint matrix of the dispatch linear program

For the rational data of a dispatch problem, the rational LP matrix is `[F, -F]`, with `F` the
[rational constraint matrix on generation and angles](rat-free-constraint-matrix.md) acting on the
positive parts and `-F` on the negative parts. The rational objects copy the real ones entrywise, so
that the checker is computable; the [casting lemmas](rat-lp-matrix-map.md) identify them with the
real linear program.
