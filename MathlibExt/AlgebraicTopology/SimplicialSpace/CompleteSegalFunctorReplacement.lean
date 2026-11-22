/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalFunctorComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.FirstProjectionClosedCoherence

/-!
# Replacement compatibility of the actual one-fold functor comparison

Restriction and postcomposition preserve weak maps in the actual Cartesian
Rezk model. The specified comparison transfers this to the native Joyal
functor object and its equivalence-edge core. Localization retains each
supplied replacement map and compares two choices through the same source.
-/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalClosed Opposite
open scoped MonoidalCategory SimplicialSpace.Cartesian SSet.modelCategoryQuillen

namespace SimplicialSpace.FirstProjection

private local instance selectedRezk : ModelCategory SimplicialSpace.{u} := RezkModel.modelCategory
private local instance selectedJoyal : ModelCategory JoyalSSet.{u} := JoyalSSet.modelCategory

/-- Any actual Rezk weak source map restricts the complete CSS power weakly. -/
theorem power_source_rezkWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hf : rezkWeakEquivalences f) (U : SimplicialSpace.{u}) (hU : completeSegalSpaces U) :
    rezkWeakEquivalences ((pre f).app U) := by
  let _ : IsClosedSymmetricMonoidalModelCategory SimplicialSpace.{u} :=
    TrueSpacePowerPreparation.actualRezk_closedSymmetricMonoidalModel
  let _ : IsCofibrant W := TrueSpacePowerPreparation.actualRezk_isCofibrant W
  let _ : IsCofibrant V := TrueSpacePowerPreparation.actualRezk_isCofibrant V
  let _ : IsFibrant U := (RezkModel.isFibrant_iff_completeSegalSpaces U).mpr hU
  have hw : WeakEquivalence f := by
    rw [weakEquivalence_iff]
    change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences f
    rwa [RezkModel.modelCategory_weakEquivalences]
  have h := (weakEquivalence_iff _).mp (weakEquivalence_pre_app_of_cofibrant (Z := U) f hw)
  change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences _ at h
  rwa [RezkModel.modelCategory_weakEquivalences] at h

/-- Postcomposition preserves an actual weak map between genuinely complete CSS targets. -/
theorem power_target_rezkWeak (W : SimplicialSpace.{u}) {V U : SimplicialSpace.{u}}
    (g : V ⟶ U) (hV : completeSegalSpaces V) (hU : completeSegalSpaces U)
    (hg : rezkWeakEquivalences g) : rezkWeakEquivalences ((ihom W).map g) := by
  let _ : IsClosedSymmetricMonoidalModelCategory SimplicialSpace.{u} :=
    TrueSpacePowerPreparation.actualRezk_closedSymmetricMonoidalModel
  let _ : IsCofibrant W := TrueSpacePowerPreparation.actualRezk_isCofibrant W
  let _ : IsFibrant V := (RezkModel.isFibrant_iff_completeSegalSpaces V).mpr hV
  let _ : IsFibrant U := (RezkModel.isFibrant_iff_completeSegalSpaces U).mpr hU
  let _ : WeakEquivalence g := by
    rw [weakEquivalence_iff]
    change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences g
    rwa [RezkModel.modelCategory_weakEquivalences]
  let _ : (ihom.adjunction W).IsQuillenAdjunction :=
    ihomAdjunction_isQuillenAdjunction_of_isCofibrant W
  have h := (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := ihom.adjunction W) g)
  change RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences _ at h
  rwa [RezkModel.modelCategory_weakEquivalences] at h

/-- The same literal restriction of native Joyal functors is categorically weak. -/
theorem native_source_categoricalWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) (hf : rezkWeakEquivalences f)
    (U : SimplicialSpace.{u}) (hU : completeSegalSpaces U) :
    SSet.categoricalEquivalences ((pre (right.map f)).app (right.obj U)) := by
  apply SSet.categoricalEquivalences.of_precomp _ _ (comparison_categoricalEquivalence V U hV hU)
  rw [← comparison_source f U]
  exact SSet.categoricalEquivalences.comp_mem _ _
    (right_categoricalWeak _ (TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal V U hU)
      (TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal W U hU)
      (power_source_rezkWeak f hf U hU)) (comparison_categoricalEquivalence W U hW hU)

/-- The same native target map is categorically weak, with its original target action. -/
theorem native_target_categoricalWeak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W)
    {V U : SimplicialSpace.{u}} (g : V ⟶ U) (hV : completeSegalSpaces V)
    (hU : completeSegalSpaces U) (hg : rezkWeakEquivalences g) :
    SSet.categoricalEquivalences ((ihom (right.obj W)).map (right.map g)) := by
  apply SSet.categoricalEquivalences.of_precomp _ _ (comparison_categoricalEquivalence W V hW hV)
  rw [← comparison_target W g]
  exact SSet.categoricalEquivalences.comp_mem _ _
    (right_categoricalWeak _ (TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal W V hV)
      (TrueSpacePowerPreparation.arbitrarySpacePower_completeSegal W U hU)
      (power_target_rezkWeak W g hV hU hg)) (comparison_categoricalEquivalence W U hW hU)

/-- Every allowed source replacement acts weakly on the same native functor core. -/
theorem native_source_coreWeak {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) (hf : rezkWeakEquivalences f)
    (U : SimplicialSpace.{u}) (hU : completeSegalSpaces U) :
    SSet.realizationWeakEquivalences
      (SSet.coreFunctor.map ((pre (right.map f)).app (right.obj U))) := by
  let _ : SSet.Quasicategory ((ihom (right.obj V)).obj (right.obj U)) :=
    comparison_target_quasicategory V U hU
  let _ : SSet.Quasicategory ((ihom (right.obj W)).obj (right.obj U)) :=
    comparison_target_quasicategory W U hU
  change SSet.realizationWeakEquivalences (SSet.core.map ((pre (right.map f)).app (right.obj U)))
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
    (SSet.core_map_mem_W_of_categoricalEquivalence (native_source_categoricalWeak f hW hV hf U hU))

/-- Every allowed target replacement keeps its weak action on the actual native functor core. -/
theorem native_target_coreWeak (W : SimplicialSpace.{u}) (hW : completeSegalSpaces W)
    {V U : SimplicialSpace.{u}} (g : V ⟶ U) (hV : completeSegalSpaces V)
    (hU : completeSegalSpaces U) (hg : rezkWeakEquivalences g) :
    SSet.realizationWeakEquivalences
      (SSet.coreFunctor.map ((ihom (right.obj W)).map (right.map g))) := by
  let _ : SSet.Quasicategory ((ihom (right.obj W)).obj (right.obj V)) :=
    comparison_target_quasicategory W V hV
  let _ : SSet.Quasicategory ((ihom (right.obj W)).obj (right.obj U)) :=
    comparison_target_quasicategory W U hU
  change SSet.realizationWeakEquivalences (SSet.core.map ((ihom (right.obj W)).map (right.map g)))
  exact (SSet.KanComplex.W_iff_realizationWeakEquivalence _).mp
    (SSet.core_map_mem_W_of_categoricalEquivalence (native_target_categoricalWeak W hW g hV hU hg))

end SimplicialSpace.FirstProjection
