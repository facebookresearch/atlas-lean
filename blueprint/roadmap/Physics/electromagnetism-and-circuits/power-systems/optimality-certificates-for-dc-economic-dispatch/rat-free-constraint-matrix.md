# Rational constraint matrix on generation and angles

For a network with rational susceptances, generators at buses and a reference bus, the rational
constraint matrix on `(p, θ)` stacks the same blocks, in the same order, as the real
[constraint matrix](../dc-economic-dispatch-as-a-linear-program/free-constraint-matrix.md): the two
balance blocks, the two reference rows, the two generator-limit blocks and the two flow-limit
blocks, built from the rational generator incidence, weighted Laplacian, reference row and
branch-flow matrix. The rational linear program that the exact checker assembles from such data
casts to the real one built from the cast data: [matrix](rat-lp-matrix-map.md),
[right-hand side](cast-vec-rat-lp-rhs.md), [objective](cast-vec-rat-lp-objective.md) and
[encoded point](cast-vec-rat-encode.md).
