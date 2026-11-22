/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBoundarySourceScalarPresentation
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarPresentationOriginalUnitWeak
import MathlibExt.AlgebraicTopology.SimplicialCategory.CofibrantUnitRetractTransfer
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarUnderHomWeakFromBase
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidComponents
import MathlibExt.AlgebraicTopology.SimplicialCategory.ScalarGroupoidCompletionStrictComparison
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedDwyerKanTwoOutOfThree

/-!
# Genuine original cofibrant homotopy-groupoid completion unit weakness

The SAME original boundary factorization source is proved degreewise free
on its actual original cell generators. Its SAME native scalar unit nerve
is therefore weak in every degree, so its SAME full original base unit
map is weak. For original groupoid components the genuine sharp Hom-fibre
criterion gives weakness of every original unit Hom. Original cofibrancy
then supplies the genuine original natural-unit retract to C.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
open ScalarGroupoidCompletion
attribute [local instance] FixedObjectModel.modelCategory
variable {O : Type u} (C : FixedObjects O)

/-- Every SAME original boundary-source scalar unit nerve is genuinely weak. -/
theorem sourceUnit_scalar_weak (q : SimplexCategoryᵒᵖ) :
    SSet.realizationWeakEquivalences (nerveMap (SSet.scalarFunctor (unit (cofibrantSource C).val) q)) :=
  originalUnit_scalar_weak (cofibrantSource C) q (boundarySourceScalarPresentation C q)

/-- The SAME original boundary-source full base unit map is genuinely weak. -/
theorem sourceUnit_base_weak :
    SSet.realizationWeakEquivalences (SSet.ScalarUnderCategory.baseMap (unit (cofibrantSource C).val)) :=
  SSet.simplicialDiagonal_map_mem_realizationWeakEquivalences _
    (fun n => sourceUnit_scalar_weak C (op ⦋n⦌))

/-- The SAME original boundary right map is genuinely weak in the full original fixed-object model. -/
theorem projection_fixedWeak : FixedObjectModel.weakEquivalences O (cofibrantProjection C) :=
  (FixedObjectModel.weakEquivalences_original_iff _).mpr
    (fun x y => (boundary_p_original (initial.to C) x y).2)

/-- The SAME original boundary source retains the original component groupoid. -/
theorem source_component_groupoid [IsGroupoid (ComponentCategory.objects.{u} C.val)] :
    IsGroupoid (ComponentCategory.objects.{u} (cofibrantSource C).val) := by
  have h := (EnrichedDwyerKan.fixedWeak_iff (cofibrantProjection C)).mpr (projection_fixedWeak C)
  let F := ComponentCategory.mapFunctor (cofibrantProjection C).val
  let _ : F.ReflectsIsomorphisms :=
    (EnrichedDwyerKan.componentFullyFaithful (cofibrantProjection C).val h.1).reflectsIsomorphisms
  exact isGroupoid_of_reflects_iso F

/-- Every SAME full original boundary-source unit Hom is weak under the genuine homotopy-groupoid hypothesis. -/
theorem sourceUnit_hom_weak [IsGroupoid (ComponentCategory.objects.{u} C.val)]
    (x y : (cofibrantSource C).val) :
    SSet.realizationWeakEquivalences ((unit (cofibrantSource C).val).map x y) := by
  let _ := source_component_groupoid C
  let _ : IsGroupoid (ComponentCategory.objects.{u} (object (cofibrantSource C).val)) :=
    ComponentCategory.isGroupoid_of_zeroScalarGroupoid (object (cofibrantSource C).val)
  exact SSet.ScalarUnderCategory.homMap_weak_of_baseMap _ (sourceUnit_base_weak C) x y

/-- The SAME original boundary-source unit is genuinely weak in the original fixed-object model. -/
theorem sourceUnit_fixedWeak [IsGroupoid (ComponentCategory.objects.{u} C.val)] :
    FixedObjectModel.weakEquivalences O (fixedUnit (cofibrantSource C)) := by
  rw [FixedObjectModel.weakEquivalences_original_iff, fixedUnit_val]
  exact sourceUnit_hom_weak C

/-- The SAME original full completion unit is genuinely weak for original cofibrant homotopy-groupoid inputs. -/
theorem cofibrantUnit_fixedWeak [IsCofibrant C] [IsGroupoid (ComponentCategory.objects.{u} C.val)] :
    FixedObjectModel.weakEquivalences O (fixedUnit C) :=
  completionUnit_weak_of_source C (sourceUnit_fixedWeak C)

/-- Every SAME complete original unit Hom is genuinely weak, at each original vertex pair. -/
theorem cofibrantUnit_hom_weak [IsCofibrant C] [IsGroupoid (ComponentCategory.objects.{u} C.val)]
    (x y : C.val) : SSet.realizationWeakEquivalences ((unit C.val).map x y) := by
  have h := (FixedObjectModel.weakEquivalences_original_iff (fixedUnit C)).mp (cofibrantUnit_fixedWeak C)
  rw [fixedUnit_val C] at h
  exact h x y

/-- The SAME original whole completion unit is genuinely DK weak. -/
theorem cofibrantUnit_DKweak [IsCofibrant C] [IsGroupoid (ComponentCategory.objects.{u} C.val)] :
    EnrichedDwyerKan.weakEquivalences (unit C.val) := by
  have h := (EnrichedDwyerKan.fixedWeak_iff (fixedUnit C)).mpr (cofibrantUnit_fixedWeak C)
  rw [fixedUnit_val C] at h
  exact h

end CategoryTheory.SimplicialEnrichment.FixedObjects.FreeFactorization
