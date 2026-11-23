/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeLefschetz

@[expose] public section

/-!
# Tests for the relative Lefschetz operators

The zeroth shifted power of a degree-two map is the canonical identification
`K ≅ K⟦0⟧`, its first power is the map itself followed by the canonical
identification of shifts, and the powers of the zero map vanish from the first
on. The relative projective space lies over its base and over `ℙⁿ`, and the
classifying map of a relative embedding factors through it.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.PerverseSheaves
open MathlibExt.AlgebraicGeometry.RelativeLefschetz
open MathlibExt.AlgebraicGeometry.DeCataldoMiglioriniDecompositionWanted (projectiveSpace)

namespace MathlibExtTest.AlgebraicGeometry.RelativeLefschetz

section Power

variable {C : Type*} [Category* C] [HasShift C ℤ] (K : C) (η : K ⟶ K⟦(2 : ℤ)⟧)

/-- The zeroth power is the canonical identification `K ≅ K⟦0⟧`. -/
example : degreeTwoPower K η 0 = (shiftFunctorZero C ℤ).inv.app K := rfl

example : IsIso (degreeTwoPower K η 0) := by
  rw [degreeTwoPower]
  infer_instance

/-- The first power is `η` followed by canonical identifications of shifts. -/
example : degreeTwoPower K η 1 =
    (shiftFunctorZero C ℤ).inv.app K ≫ η⟦2 * ((0 : ℕ) : ℤ)⟧' ≫
      (shiftFunctorAdd' C (2 : ℤ) (2 * ((0 : ℕ) : ℤ)) (2 * ((0 + 1 : ℕ) : ℤ))
        (by omega)).inv.app K := rfl

/-- The powers of the zero map vanish from the first on. -/
example [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive] (k : ℕ) :
    degreeTwoPower K 0 (k + 1) = 0 := by
  simp [degreeTwoPower]

end Power

/-- The relative projective space lies over the base. -/
example (Y : PerverseSheaves.ComplexScheme) (n : ℕ) :
    (relativeProjectiveSpace Y n).hom = (toBase Y n).left ≫ Y.hom := rfl

/-- Its projection to `ℙⁿ` is compatible with the structure maps. -/
example (Y : PerverseSheaves.ComplexScheme) (n : ℕ) :
    (toProjectiveSpace Y n).left ≫ (projectiveSpace n).hom =
      (relativeProjectiveSpace Y n).hom :=
  (toProjectiveSpace Y n).w

/-- The classifying map of a relative embedding is the embedding followed by
the projection to `ℙⁿ`. -/
example {X Y : PerverseSheaves.ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) :
    E.classifyingMap = E.embedding ≫ toProjectiveSpace Y n := rfl

/-- The embedding lies over `Y`. -/
example {X Y : PerverseSheaves.ComplexScheme} {f : X ⟶ Y} {n : ℕ}
    (E : RelativeProjectiveEmbedding f n) : E.embedding ≫ toBase Y n = f := E.over

end MathlibExtTest.AlgebraicGeometry.RelativeLefschetz
