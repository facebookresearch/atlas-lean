/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidPathEquifibred
import MathlibExt.AlgebraicTopology.SimplicialSet.RezkDiagonalSharpHomotopyPullback

/-!
# The actual fixed-object Segal groupoid path diagonal is sharp

All original path rows are sharp at genuine Reedy fibrancy. The
original Segal groupoid transition edges supply every whole operator
relative weak comparison. Rezk's proved original diagonal theorem then
gives sharpness of the literal path projection diagonal and all its
native row-vertex homotopy-pullback comparisons.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped Simplicial SSet.modelCategoryQuillen

namespace SimplicialSpace.LeftDecalageObject

open SimplicialSpace.SegalHomotopy

/-- The literal whole diagonal of the original fixed-object path projection. -/
abbrev diagonalProjection (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.simplicialDiagonalFunctor.obj (diagram W x) ⟶ SSet.simplicialDiagonalFunctor.obj W.diagram :=
  SSet.simplicialDiagonalFunctor.map (projection W x)

/-- The whole original Segal-groupoid path projection has its genuine diagonal sharpness and row comparisons. -/
theorem diagonal_sharp_and_row_comparisons (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hG : ∀ a : (W.diagram _⦋1⦌) _⦋0⦌, IsEquivalenceEdge W hW a)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.SharpComparisonDraft.Sharp (diagonalProjection W x) ∧
      ∀ (n : SimplexCategory) (v : Fin (n.len + 1)), WeakEquivalence
        (SSet.RezkOriginal61.kappa (projection W x) n v) := by
  let _ : ModelCategory SimplicialSpace.{u} := ReedyModel.modelCategory
  have h := SSet.RezkOriginal61.all_simplex_sharp_and_native_homotopy_pullback (projection W x)
    (fun n => projection_sharp W x hW.1 n.len)
    (by
      intro n m f
      apply (HomotopicalAlgebra.weakEquivalence_iff _).mpr
      exact relativeOperatorComparison_weak W hW hG x f)
  exact ⟨h.2.1, h.2.2⟩

end SimplicialSpace.LeftDecalageObject
