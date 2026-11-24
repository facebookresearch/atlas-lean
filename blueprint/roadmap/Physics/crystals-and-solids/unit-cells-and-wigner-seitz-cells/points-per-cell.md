# Points Per Cell

The number of lattice points of `Λf` per conventional cell of `Λc`, as a quotient count: the
cardinality of the quotient of the fine lattice by the coarse sublattice (the index). It is not
the number of `Λf` points in the closed set `conventionalCell Λc`. Meaningful when
`IsSublatticeOf Λc Λf`, in which case `pointsPerCell_eq_volume_ratio` shows it equals
`V_conv / V_prim`.
