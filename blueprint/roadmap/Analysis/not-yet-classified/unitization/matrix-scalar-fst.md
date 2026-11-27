# Matrix Scalar Fst

Let `A` be a possibly nonunital complex C*-algebra. Let `ι` be a finite index type.
Scalar-coordinate projection out of the unitization of a matrix algebra: the
`Unitization.fstStarAlgHom` projection at the matrix coefficient algebra, bundled directly from
`Unitization.fstHom`. Stating `Unitization.fstStarAlgHom (CStarMatrix ι ι A)` requires a
`NonUnitalCStarAlgebra (CStarMatrix ..)` instance, whose Mathlib construction needs a `PartialOrder`
and `StarOrderedRing` on `A` (the canonical spectral order) together with nondefault transparency to
reconcile the projected instances with the direct matrix instances. Naming the bundled hom here pins
that elaboration once: the scalar squares in this file and on projection `K0` are stated against
this hom with plain `[NonUnitalCStarAlgebra A]`, and its action is first projection by
`matrixScalarFst_apply`.
