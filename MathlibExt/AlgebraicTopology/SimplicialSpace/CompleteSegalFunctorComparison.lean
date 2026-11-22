/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.FirstProjectionClosedComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalQuasicategoryCoreComparison
import MathlibExt.AlgebraicTopology.Quasicategory.CoreWeakEquivalence
import MathlibExt.AlgebraicTopology.ModelCategory.InternalHomSourceWeakEquivalence

/-!
# The actual one-fold CSS-to-Joyal functor comparison

For genuine fibrant CSS sources and targets, restriction along the original
first-JT counit is weak in the actual Cartesian Rezk model. The actual right
Quillen functor preserves that weakness between the two complete powers.
The whole first-projection power Iso gives the specified categorical
equivalence to the native Joyal functor quasicategory. Its native core map
is weak by the established categorical-equivalence core theorem.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace SimplicialSpace.FirstProjection

private local instance selectedRezk : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
private local instance selectedJoyal : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory

/-- Genuine source completeness makes the actual first-projection counit Rezk weak. -/
theorem counit_rezkWeak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W) :
    rezkWeakEquivalences (counit W) := by
  let e := comparisonLeft.mapIso
    (JoyalSSet.equivalenceSSet.unitIso.app (comparisonRight.obj W))
  have h : rezkWeakEquivalences (e.inv ≫ comparisonAdjunction.counit.app W) :=
    rezkWeakEquivalences.comp_mem _ _ (rezkWeakEquivalences.of_isIso e.inv)
      (comparisonAdjunction_counit_rezkWeak W hW)
  exact (counit_eq W).symm ▸ h

/-- The actual source counit restricts the full CSS power by a Rezk weak map. -/
theorem powerCounit_rezkWeak (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    rezkWeakEquivalences ((MonoidalClosed.pre (counit W)).app V) := by
  let _ : IsClosedSymmetricMonoidalModelCategory SimplicialSpace.{u} :=
    TrueSpacePowerPreparation.actualRezk_closedSymmetricMonoidalModel
  let _ : IsCofibrant (left.obj (right.obj W)) := TrueSpacePowerPreparation.actualRezk_isCofibrant _
  let _ : IsCofibrant W := TrueSpacePowerPreparation.actualRezk_isCofibrant W
  let _ : IsFibrant V := (RezkModel.isFibrant_iff_completeSegalSpaces V).mpr hV
  have hc : WeakEquivalence (counit W) := by
    rw [weakEquivalence_iff]
    change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences _
    rw [RezkModel.modelCategory_weakEquivalences]
    exact counit_rezkWeak W hW
  have hp : WeakEquivalence ((MonoidalClosed.pre (counit W)).app V) :=
    weakEquivalence_pre_app_of_cofibrant (Z := V) (counit W) hc
  have h := (weakEquivalence_iff _).mp hp
  change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences _ at h
  rwa [RezkModel.modelCategory_weakEquivalences] at h

/-- The actual first-JT right functor preserves Rezk weak maps between complete CSS objects. -/
theorem right_categoricalWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) (hf : rezkWeakEquivalences f) :
    SSet.categoricalEquivalences (right.map f) := by
  let _ : comparisonAdjunction.{u}.IsQuillenAdjunction := comparisonAdjunction_isQuillen
  let _ : IsFibrant W := (RezkModel.isFibrant_iff_completeSegalSpaces W).mpr hW
  let _ : IsFibrant V := (RezkModel.isFibrant_iff_completeSegalSpaces V).mpr hV
  let _ : WeakEquivalence f := by
    rw [weakEquivalence_iff]
    change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences f
    rwa [RezkModel.modelCategory_weakEquivalences]
  have h := (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := comparisonAdjunction) f)
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences
    (comparisonRight.map f) at h
  rwa [JoyalSSet.modelCategory_weakEquivalences] at h

/-- The literal CSS functor-object comparison is a categorical equivalence for arbitrary fibrant CSS endpoints. -/
theorem comparison_categoricalEquivalence (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    SSet.categoricalEquivalences (comparison W V) := by
  unfold comparison
  exact SSet.categoricalEquivalences.comp_mem _ _
    (right_categoricalWeak _ (TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal W V hV)
      (TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal (left.obj (right.obj W)) V hV)
        (powerCounit_rezkWeak W V hW hV))
    (SSet.categoricalEquivalences.of_isIso _)

/-- The comparison's source is the actual first-JT quasicategory of the complete CSS power. -/
theorem comparison_source_quasicategory (W V : SimplicialSpace.{u}) (hV : completeSegalSpaces V) :
    SSet.Quasicategory (right.obj ((ihom W).obj V)) :=
  OnefoldCoreComparison.row_isQuasicategory _
    (TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal W V hV)

/-- The native scalar functor object is a quasicategory at every genuine fibrant CSS target. -/
theorem comparison_target_quasicategory (W V : SimplicialSpace.{u}) (hV : completeSegalSpaces V) :
    SSet.Quasicategory ((ihom (right.obj W)).obj (right.obj V)) := by
  let e := (functorObjectIso (right.obj W)).app V
  have hq := comparison_source_quasicategory (left.obj (right.obj W)) V hV
  let a : Arrow.mk (terminal.from (right.obj ((ihom (left.obj (right.obj W))).obj V))) ≅
      Arrow.mk (terminal.from ((ihom (right.obj W)).obj (right.obj V))) :=
    Arrow.isoMk e (Iso.refl _) (by exact terminal.hom_ext _ _)
  exact (SSet.categoricalFibrations.terminalFrom_iff_quasicategory _).mp
    ((SSet.categoricalFibrations.arrow_mk_iso_iff a).mp
      ((SSet.categoricalFibrations.terminalFrom_iff_quasicategory _).mpr hq))

/-- The actual categorical comparison restricts to the same weak native-core map. -/
theorem comparison_coreWeak (W V : SimplicialSpace.{u})
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    SSet.realizationWeakEquivalences (SSet.coreFunctor.map (comparison W V)) := by
  let _ : SSet.Quasicategory (right.obj ((ihom W).obj V)) := comparison_source_quasicategory W V hV
  let _ : SSet.Quasicategory ((ihom (right.obj W)).obj (right.obj V)) :=
    comparison_target_quasicategory W V hV
  change SSet.realizationWeakEquivalences (SSet.core.map (comparison W V))
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
    (SSet.core_map_mem_W_of_categoricalEquivalence (comparison_categoricalEquivalence W V hW hV))

end SimplicialSpace.FirstProjection
