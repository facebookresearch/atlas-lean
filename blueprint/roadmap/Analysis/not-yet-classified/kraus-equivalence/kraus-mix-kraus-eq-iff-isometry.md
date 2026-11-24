# Kraus mix Kraus eq iff isometry

For a linearly independent Kraus family `K`, the mixed family `mixKraus U K`
defines the same CP map as `K` exactly when `U` is an isometry.

Rows of `U : Matrix s r ℂ` index the target family `mixKraus U K` and columns
index the source family `K`: `(mixKraus U K) j = ∑ i, U j i • K i` with no
conjugation on `U j i`. The isometry condition is `Uᴴ * U = 1`. Empty
`r = Fin 0` is supported: the empty-column matrix is isometric and forces the
target to be zero.
