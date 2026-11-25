# Rational weighted Laplacian of a network

For a network with rational susceptances `b`, the rational weighted Laplacian is `B diag(b) Bᵀ`,
with `B` the [rational incidence matrix](rat-incidence.md). The rational linear program that the
exact checker assembles from such data casts to the real one built from the cast data:
[matrix](rat-lp-matrix-map.md), [right-hand side](cast-vec-rat-lp-rhs.md),
[objective](cast-vec-rat-lp-objective.md) and [encoded point](cast-vec-rat-encode.md).
