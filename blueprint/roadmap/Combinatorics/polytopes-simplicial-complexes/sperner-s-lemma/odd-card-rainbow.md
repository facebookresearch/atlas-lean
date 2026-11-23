# Sperner's lemma in dimension two (parity form)

For every Sperner colouring $c$ of the grid triangle with corners $(0, 0)$, $(n, 0)$ and $(0, n)$,
the number of rainbow cells of the grid triangulation, up cells plus down cells, is odd.

This is the two-dimensional case of E. Sperner, "Neuer Beweis für die Invarianz der
Dimensionszahl und des Gebietes", Abh. Math. Sem. Univ. Hamburg 6 (1928), 265–272, for the
particular triangulation by the unit grid; Sperner proves it for arbitrary triangulations of a
simplex. The proof counts modulo $2$ the doors, the unit edges coloured $0$ and $1$.

## Informally uses

- [Sperner's lemma in dimension one](odd-card-bichromatic.md): the bottom side, coloured with $0$ and $1$ from corner to corner, carries an odd number of doors.

## Background

- [Every END-OF-THE-LINE instance has a sink](../../../TheoryOfComputation/completeness-other-classes/ppad-and-the-end-of-the-line-problem/exists-sink.md): the directed parity principle that the door-to-door walk instantiates.
- [Knaster–Kuratowski–Mazurkiewicz lemma](../../../Geometry/convex-geometry/kkm-lemma.md): the $n$-dimensional lemma on barycentric subdivisions is its main step.
