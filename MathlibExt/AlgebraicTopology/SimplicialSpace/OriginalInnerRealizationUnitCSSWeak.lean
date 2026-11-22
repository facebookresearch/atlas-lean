/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalInnerRealizationQuillen
import MathlibExt.AlgebraicTopology.SimplicialSpace.CSSValuedSimplexReedyAdapter
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalFullJPowerSectionCompleteTargetTests
import MathlibExt.AlgebraicTopology.SimplicialSpace.OriginalBaselineUnitRezkWeak
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkCompletionUnitData
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown

/-!
# The literal original completion unit is weak on every complete-target CSS test

The actual INNER coend is left Quillen by its derived cotensor matching
corners. Both complete coefficient diagrams are Reedy cofibrant by the
actual Set-EZ/evaluation proof. Ken Brown therefore preserves the original
row section weak maps, whose all-complete-target proofs use literal E
contractions and strict Arrow retracts.

The already constructed coend/diagonal Isos identify this exact coend map
with the original Raw20 unit. The same unlocalized baseline beta is Reedy
weak, hence Rezk weak. Their unchanged Unit9 composite is consequently
tested weak by every complete target. No Segalness, DK recognition,
replacement-unit weakness or diagonal-preservation outcome is supplied.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped Simplicial SimplicialSpace.Inner

namespace SimplicialSpace.OriginalInnerRealization

/-- The actual coend functor acts by the original complete bifunctor map. -/
theorem innerRealizationFunctor_map_eq_coendMap
    {X Y : SimplicialObject SimplicialSpace.{u}} (f : X ⟶ Y) :
    innerRealizationFunctor.map f = coend.map (innerRealizationBifunctorMap f) := rfl

/-- Derived Reedy cofibrancy and the actual Quillen adjunction preserve all original row weak
maps. -/
theorem innerRealization_coendMap_rezkWeak
    {X Y : SimplicialObject SimplicialSpace.{u}} (f : X ⟶ Y)
    (hrows : ∀ m : SimplexCategoryᵒᵖ, rezkWeakEquivalences (f.app m)) :
    rezkWeakEquivalences (coend.map (innerRealizationBifunctorMap f)) := by
  let : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
  let _ : HasInitial SimplicialSpace.{u} :=
    (RezkModel.modelCategory.cm1b).out (Discrete PEmpty.{1})
  let _ : HasInitial (SimplicialObject SimplicialSpace.{u}) :=
    functorCategoryHasColimitsOfShape (J := Discrete PEmpty.{1})
      (K := SimplexCategoryᵒᵖ) (C := SimplicialSpace.{u})
  let : ModelCategory (SimplicialObject SimplicialSpace.{u}) :=
    SimplicialObject.reedyModelCategory
  let : Adjunction.IsQuillenAdjunction innerRealizationAdjunction :=
    innerRealizationAdjunction_isQuillen
  let : IsCofibrant X := CSSValuedSimplexReedyAdapter.css_simplex_all_objects_reedy_cofibrant X
  let : IsCofibrant Y := CSSValuedSimplexReedyAdapter.css_simplex_all_objects_reedy_cofibrant Y
  let : WeakEquivalence f := by
    rw [HomotopicalAlgebra.weakEquivalence_iff]
    change ∀ m : SimplexCategoryᵒᵖ,
      RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences (f.app m)
    rw [RezkModel.modelCategory_weakEquivalences]
    exact hrows
  have hw : WeakEquivalence (innerRealizationFunctor.map f) :=
    Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant
      (adj := innerRealizationAdjunction) f
  have h := (HomotopicalAlgebra.weakEquivalence_iff _).mp hw
  change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (innerRealizationFunctor.map f) at h
  rw [RezkModel.modelCategory_weakEquivalences, innerRealizationFunctor_map_eq_coendMap] at h
  exact h

/-- The actual INNER coend of the original full-J section is Rezk weak for every W. -/
theorem originalConstantSection_coendMap_rezkWeak (W : SimplicialSpace.{u}) :
    rezkWeakEquivalences
      (coend.map (innerRealizationBifunctorMap (RezkCompletionRaw.constantPowerSection W))) :=
  innerRealization_coendMap_rezkWeak (RezkCompletionRaw.constantPowerSection W)
    (OriginalFullJSectionTests.constantPowerSection_rezkWeak W)

/-- The unchanged Raw20 unit is weak by its literal INNER-coend identity and genuine constructed
Isos. -/
theorem rawCompletionUnit_rezkWeak (W : SimplicialSpace.{u}) :
    rezkWeakEquivalences (RezkCompletionRaw.rawCompletionUnit W) := by
  rw [← innerRealization_original_raw_unit]
  exact rezkWeakEquivalences.comp_mem _ _
    (rezkWeakEquivalences.of_isIso (innerDiagonalConstIso W).inv)
    (rezkWeakEquivalences.comp_mem _ _
      (rezkWeakEquivalences.of_isIso
        (innerRealizationDiagonalIso ((SimplicialObject.const SimplicialSpace.{u}).obj W)).inv)
      (rezkWeakEquivalences.comp_mem _ _ (originalConstantSection_coendMap_rezkWeak W)
        (rezkWeakEquivalences.of_isIso
          (innerRealizationDiagonalIso (RezkCompletionRaw.powerDiagram W)).hom)))

end SimplicialSpace.OriginalInnerRealization

namespace SimplicialSpace.RezkCompletionData

/-- The SAME original unit, rawUnit followed by its ONE unlocalized beta, is genuinely CSS weak. -/
theorem unit_rezkWeak (W : SimplicialSpace.{u}) : rezkWeakEquivalences (unit.app W) := by
  rw [unit_app]
  exact rezkWeakEquivalences.comp_mem _ _
    (OriginalInnerRealization.rawCompletionUnit_rezkWeak W)
    (OriginalUnitCSSWeak.baselineUnit_rezkWeak (RezkCompletionRaw.rawCompletion W))

/-- Every original complete target sees realization weakness of the unchanged unit's whole inner
test. -/
theorem unit_all_complete_target_tests (W Z : SimplicialSpace.{u})
    (hZ : completeSegalSpaces Z) :
    SSet.realizationWeakEquivalences ((innerHomFunctor.map (unit.app W).op).app Z) :=
  unit_rezkWeak W Z hZ

end SimplicialSpace.RezkCompletionData
