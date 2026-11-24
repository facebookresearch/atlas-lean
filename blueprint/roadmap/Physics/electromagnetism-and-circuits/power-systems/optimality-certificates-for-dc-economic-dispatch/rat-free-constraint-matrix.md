# Rational constraint matrix on generation and angles

For a network with rational susceptances, generators at buses and a reference bus, the rational
constraint matrix on `(p, θ)` stacks the same blocks, in the same order, as the real
[constraint matrix](../dc-economic-dispatch-as-a-linear-program/free-constraint-matrix.md): the two
balance blocks, the two reference rows, the two generator-limit blocks and the two flow-limit
blocks, built from the rational generator incidence, weighted Laplacian, reference row and
branch-flow matrix. Its entries are given by the same formula as for the real linear program, over
the rationals, so that the checker is an exact finite test. The cast of the assembled rational
program is the real one: [matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
