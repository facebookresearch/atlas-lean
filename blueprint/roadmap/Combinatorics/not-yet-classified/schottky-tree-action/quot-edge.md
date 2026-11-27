# Oriented quotient edges

The set of orbits of darts of `𝒯` under `G`: the oriented
edges of the quotient graph. An edge of `𝒯` has two darts, one for each orientation. When no
element of `G` sends one to the other, they lie in two orbits and the quotient keeps both
orientations: for the translation action of `ℤ` on the integer path graph, the quotient has
one vertex and one unoriented loop, but two oriented edges. When some element of `G` inverts
the edge, that is, sends one of its darts to the reverse dart, both darts lie in one orbit,
which `quotientReversal` fixes.
