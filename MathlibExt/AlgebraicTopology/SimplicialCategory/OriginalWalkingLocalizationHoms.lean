/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalWalkingArrowCompletionHoms
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalWalkingArrowFreeSingleHomIso
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCompletionLocalizationLift
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalUnitHomWeakTransport

/-!
# Every full Hom of the actual walking-arrow localization pullback is weak to the unit

The same original two-label free arrow completes isomorphically to the
actual walking-arrow completion. The genuine native horn inclusion and
literal localization pullback projection transfer this full Hom result
to their SAME original middle object and pullback. All actual factors,
unit maps, individual object labels and full coefficient maps remain.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra MonoidalCategory

namespace CategoryTheory.SimplicialEnrichment.OriginalWalkingLocalizationHoms
open FixedObjects ScalarGroupoidCompletion OriginalWalkingArrowFreeSingleHomIso

/-- The actual completed original free-arrow Hom is isomorphic to the SAME unit coefficient. -/
def completedFreeHomIso (x y : walking.{u}) :
    FixedObjects.hom (fixedObject free) x y ≅ 𝟙_ SSet.{u} :=
  (FixedObjects.evaluation x y).mapIso (fixedFunctor.mapIso iso) ≪≫
    OriginalWalkingArrowCompletionHoms.homIso x y

/-- Every full original completed free-arrow Hom projection to the unit is genuinely weak. -/
theorem completedFreeHom_toUnit_weak (x y : walking.{u}) :
    SSet.realizationWeakEquivalences
      (CodiscreteEnrichment.toUnit (FixedObjects.hom (fixedObject free) x y)) := by
  have h := SSet.realizationWeakEquivalences.of_isIso (completedFreeHomIso x y).hom
  have he : (completedFreeHomIso x y).hom =
      CodiscreteEnrichment.toUnit (FixedObjects.hom (fixedObject free) x y) := by
    ext q a
    change PUnit.unit = PUnit.unit
    rfl
  exact (congrArg (fun g : FixedObjects.hom (fixedObject free) x y ⟶ 𝟙_ SSet.{u} =>
    SSet.realizationWeakEquivalences g) he).mp h

variable {C : FixedObjects walking.{u}} (F : free ⟶ C)
attribute [local instance] FixedObjectModel.modelCategory

/-- Every SAME full Hom of the retained native localization middle object is genuinely weak to the unit. -/
theorem middleHom_toUnit_weak (x y : walking.{u}) :
    SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit
      (FixedObjects.hom
        (OriginalCompletionLocalizationPullback.middle C (fixedMap F)) x y)) := by
  have h := OriginalCompletionLocalizationPullback.left_weak C (fixedMap F)
  have hxy : SSet.realizationWeakEquivalences
      (homMap (OriginalCompletionLocalizationPullback.left C (fixedMap F)) x y) :=
    (FixedObjectModel.weakEquivalences_iff _).mp h x y
  exact (CodiscreteEnrichment.toUnit_weak_iff
    (homMap (OriginalCompletionLocalizationPullback.left C (fixedMap F)) x y) hxy).mp
      (completedFreeHom_toUnit_weak x y)

/-- Every complete original Hom of the literal localization pullback is weak to the SAME original unit. -/
theorem pullbackHom_toUnit_weak [IsCofibrant C]
    [IsGroupoid (ComponentCategory.objects.{u} C.val)] (x y : walking.{u}) :
    SSet.realizationWeakEquivalences (CodiscreteEnrichment.toUnit
      (FixedObjects.hom (OriginalCompletionLocalizationLift.object F) x y)) := by
  have h := OriginalCompletionLocalizationPullback.toMiddle_weak C (fixedMap F)
  have hxy : SSet.realizationWeakEquivalences
      (homMap (OriginalCompletionLocalizationPullback.toMiddle C (fixedMap F)) x y) :=
    (FixedObjectModel.weakEquivalences_iff _).mp h x y
  exact (CodiscreteEnrichment.toUnit_weak_iff
    (homMap (OriginalCompletionLocalizationPullback.toMiddle C (fixedMap F)) x y) hxy).mpr
      (middleHom_toUnit_weak F x y)

end CategoryTheory.SimplicialEnrichment.OriginalWalkingLocalizationHoms
