# Regular Point

`w` is a regular point for the stable multiplicity of `A` and `B`: every cell of the weighted
support of `A` and every cell of the weighted support of `B` through `w` meet in a set of at least
the expected dimension
`A.dimension + B.dimension - n` (stated without natural subtraction). Equivalently, the cell of
their common refinement having `w` in its relative interior has at least the expected dimension.
Osserman--Payne (Definition 2.6.1) attach the stable multiplicity to faces of the expected
dimension; at a lower-dimensional cell of the common refinement, for instance a new vertex of a
subdivision, the raw displacement sum `stableMultiplicity` adds up several neighbouring faces and
depends on the subdivision and on the displacement.
