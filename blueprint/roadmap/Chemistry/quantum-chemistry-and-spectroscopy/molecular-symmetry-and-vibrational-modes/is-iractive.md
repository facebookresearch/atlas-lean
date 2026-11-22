# IR activity (dipole model, MOD)

A vibrational mode transforming as the irreducible
representation `σ` (an irreducible component of the internal-mode representation) is
IR-active iff `σ` occurs in the vector representation, i.e. transforms like `x`, `y` or `z`.
This is a definition inside the dipole model; it does not predict intensities or observation,
and labels of `σ` refer to the fixed axis convention of `R`. The `IsIrreducible σ` argument
is part of the predicate: activity is only defined for irreps, so a reducible `σ` with a
nonzero intertwining space cannot be classified as active. A claim about a vibrational mode
additionally requires `σ` to occur in the (complexified) internal-mode representation
`internalModeRepresentation`.
