# Stable GLMatrix Grp Iso inv of

`inv` of `stableGLMatrixGrpIso` on a finite base representative:
base-to-matrix and representative orientation, `StableGL.of g` with `g : GLₙ R`
maps to `StableGL.of ((matrixGLMulEquiv n).symm (F.map (n ≤ n*card) g))`,
i.e. padding along `n ≤ n*card ι` then de-flattening.
