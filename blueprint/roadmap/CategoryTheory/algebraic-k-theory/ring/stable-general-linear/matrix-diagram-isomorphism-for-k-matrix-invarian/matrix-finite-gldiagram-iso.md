# Matrix Finite GLDiagram Iso

Natural isomorphism
`matrixFiniteGLDiagram (R := R) (ι := ι) ≅ scaledBaseFiniteGLDiagram (R := R) (ι := ι)`
in `ℕ ⥤ GrpCat.{u}`.

Orientation: source is `matrixFiniteGLDiagram` (`n ↦ GLₙ (Matrix ι ι R)`),
target is `scaledBaseFiniteGLDiagram` (`n ↦ GL_{n * card ι} R` via
`natMulFunctor (card ι)`). At `n`, `hom` is `(matrixGLIso n).hom`, the flattening
`GLₙ (Matrix ι ι R) →* GL_{n * card ι} R` via `Matrix.comp`, and `inv` is
`(matrixGLIso n).inv`.
