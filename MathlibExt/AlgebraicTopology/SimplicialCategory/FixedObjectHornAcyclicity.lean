/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeHornCellAttachments
import MathlibExt.AlgebraicTopology.SimplicialCategory.FixedObjectModelClasses
import MathlibExt.AlgebraicTopology.SimplicialCategory.FreeGeneratingFactorizations
import MathlibExt.AlgebraicTopology.ModelCategory.OriginalGeneratedModel
import Mathlib.CategoryTheory.MorphismProperty.RetractArgument

/-!
# Actual free-horn acyclicity and the trivial-cofibration class

The word-filtration theorem applies to the real free-horn coproduct
pushouts. Actual Hom colimit preservation gives their supported
transfinite closure, and the genuine small-object/retract theorem
identifies every free-horn left map. The original factorization and
scalar two-out-of-three then prove the exact model class intersection.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectModel

variable {O : Type u}

/-- Every actual free-horn left map is anodyne on the entire original Hom objects. -/
theorem trivialCofibrations_le_homAnodyne : trivialCofibrations O ≤ homAnodyne O := by
  change (hornFamily O).rlp.llp ≤ homAnodyne O
  rw [MorphismProperty.llp_rlp_of_hasSmallObjectArgument (hornFamily O)]
  have ht : MorphismProperty.transfiniteCompositions.{u}
      (MorphismProperty.coproducts.{u} (hornFamily O)).pushouts ≤ homAnodyne O :=
    (MorphismProperty.transfiniteCompositions_monotone FreeHornCells.coproduct_pushouts_le_homAnodyne).trans
      (MorphismProperty.transfiniteCompositions_le (homAnodyne O))
  exact (MorphismProperty.retracts_monotone ht).trans (MorphismProperty.retracts_le (homAnodyne O))

/-- The same genuine free-horn left maps are weak on every original fixed-label Hom. -/
theorem trivialCofibrations_le_weakEquivalences : trivialCofibrations O ≤ weakEquivalences O := by
  intro C D f hf
  apply (weakEquivalences_iff f).mpr
  intro x y
  have h := (homAnodyne_iff f).mp (trivialCofibrations_le_homAnodyne _ hf) x y
  rw [SSet.anodyneExtensions_eq_trivialCofibrations] at h
  exact (weakEquivalence_iff _).mp ((mem_trivialCofibrations_iff _).mp h).2

/-- Every supported actual transfinite free-horn attachment preserves anodyne original Hom maps. -/
theorem transfinite_original_anodyne {J : Type u} [LinearOrder J] [SuccOrder J] [OrderBot J]
    [WellFoundedLT J] {C D : FixedObjects O} (f : C ⟶ D)
    (h : (MorphismProperty.coproducts.{u} (hornFamily O)).pushouts.TransfiniteCompositionOfShape J f) :
    ∀ a b : C.val, SSet.anodyneExtensions (f.val.map a b) := by
  let h' := h.ofLE FreeHornCells.coproduct_pushouts_le_homAnodyne
  exact (homAnodyne_original_iff f).mp ((homAnodyne O).transfiniteCompositionsOfShape_le J _
    (MorphismProperty.TransfiniteCompositionOfShape.mem _ h'))

/-- The actual left map of the stored free-horn factorization is anodyne on every original Hom. -/
theorem horn_i_original_anodyne {C D : FixedObjects O} (f : C ⟶ D) :
    ∀ a b : C.val, SSet.anodyneExtensions ((FreeFactorization.horn f).i.val.map a b) :=
  (homAnodyne_original_iff (FreeFactorization.horn f).i).mp
    (trivialCofibrations_le_homAnodyne _ (FreeFactorization.horn f).hi)

/-- The actual trivial-cofibration class is exactly actual cofibration intersected with actual Hom weakness. -/
theorem trivialCofibrations_eq : trivialCofibrations O = cofibrations O ⊓ weakEquivalences O := by
  exact OriginalGeneratedModel.left_class_eq
    (boundaryFamily O) (hornFamily O) (weakEquivalences O)
    (weak_twoOutOfThree (O := O)) (trivialFibrations_eq (O := O))
    (trivialCofibrations_le_weakEquivalences (O := O)) (FreeFactorization.hornData (O := O))

end CategoryTheory.SimplicialEnrichment.FixedObjects.FixedObjectModel
