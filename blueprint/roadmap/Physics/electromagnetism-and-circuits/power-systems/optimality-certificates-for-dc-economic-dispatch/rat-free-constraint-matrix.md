# Rational constraint matrix on generation and angles

For a network with rational susceptances, generators at buses and a reference bus, the rational
constraint matrix on `(p, θ)` stacks the same blocks, in the same order, as the real
[constraint matrix](../dc-economic-dispatch-as-a-linear-program/free-constraint-matrix.md): the two
balance blocks, the two reference rows, the two generator-limit blocks and the two flow-limit
blocks, built from the rational generator incidence, weighted Laplacian, reference row and
branch-flow matrix. The rational objects copy the real ones entrywise, so that the checker is
computable; the [casting lemmas](rat-lp-matrix-map.md) identify them with the real linear program.
