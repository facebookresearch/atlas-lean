# Stiffness Matrix free not pos Def

The stiffness matrix of a free network is not positive definite (MC): on a
nonempty node type the all-ones vector is nonzero and, by
`stiffnessMatrix_free_zeroMode`, in its kernel. `[Nonempty ι]` cannot be
dropped: on an empty node type every matrix is positive definite, vacuously.
