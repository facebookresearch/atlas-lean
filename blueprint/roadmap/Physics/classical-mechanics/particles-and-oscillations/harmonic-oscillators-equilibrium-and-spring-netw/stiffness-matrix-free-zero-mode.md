# Stiffness Matrix free zero Mode

Rigid-translation kernel identity (MC, free network only): with `w = 0` the
stiffness matrix sends the all-ones vector to `0`. On an empty node type that
vector is itself `0` and the identity is trivial; see
`stiffnessMatrix_free_not_posDef` for the nonempty case.
