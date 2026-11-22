/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalLocalScalarSM7
import MathlibExt.AlgebraicTopology.SimplicialPresheaf.OriginalRezkLocalizerComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.RezkModelCategory
import Mathlib.CategoryTheory.Comma.Arrow

/-!
# The original named CSS model and its designated inner cotensor corner

The original coefficient model and named Rezk model have already proved
equal class getters under designation. These equations transport the same
supplied native scalar cotensor pullback corner; they do not introduce a
new model or assume right-adjoint preservation. The comparison of this
designated pullback with the chosen CSS relative matching pullback remains
an actual two-projection Iso in the following matching assembly.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Opposite
open scoped SSet.modelCategoryQuillen

namespace SimplicialSpace.OriginalNamedCSSCotensor

/-- Exact global fibration getters agree under the original forget/designation pair. -/
theorem coefficientFibration_iff {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    RezkModel.modelCategory.categoryWithFibrations.fibrations p ↔
      (SimplicialPresheaf.InjectiveKan.originalLocalSmithModel
          SSet.Rezk.localizingMap.{u}).categoryWithFibrations.fibrations p.hom := by
  have h :=
      SimplicialPresheaf.OriginalRezkLocalizer.coefficientModel_classes_and_equivalence.{u}.2.2.1
  rw [h]
  rfl

/-- The same two exact global getters give trivial fibrations without a new weak class. -/
theorem coefficientTrivialFibration_iff {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    (RezkModel.modelCategory.categoryWithFibrations.fibrations ⊓
      RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences) p ↔
    ((SimplicialPresheaf.InjectiveKan.originalLocalSmithModel
        SSet.Rezk.localizingMap.{u}).categoryWithFibrations.fibrations ⊓
      (SimplicialPresheaf.InjectiveKan.originalLocalSmithModel
          SSet.Rezk.localizingMap.{u}).categoryWithWeakEquivalences.weakEquivalences) p.hom := by
  have hW :=
      SimplicialPresheaf.OriginalRezkLocalizer.coefficientModel_classes_and_equivalence.{u}.2.1
  exact and_congr (coefficientFibration_iff p) (by rw [hW]; rfl)

/-- The native parallel diagram uses precisely the original scalar cotensor restriction. -/
def coefficientCotensorParallel {K L : SSet.{u}} (j : K ⟶ L) :
    WalkingParallelPairᵒᵖ ⥤ (SimplicialPresheaf.{u} SimplexCategory) ⥤
      SimplicialPresheaf.{u} SimplexCategory :=
  walkingParallelPairOp.leftOp ⋙
    parallelPair ((SimplicialPresheaf.scalarCotensor (D := SimplexCategory)).map j.op)
      ((SimplicialPresheaf.scalarCotensor (D := SimplexCategory)).map j.op)

/-- Choose the actual native supplied pullback corner for the original global morphism. -/
def coefficientCotensorPullback {K L : SSet.{u}} (j : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) :
    (coefficientCotensorParallel j).PullbackObjObj WalkingParallelPairHom.left p.hom :=
  Functor.PullbackObjObj.ofHasPullback (coefficientCotensorParallel j)
    WalkingParallelPairHom.left p.hom

/-- Designate that same native corner arrow on the original simplicial-space carrier. -/
def designatedCotensorCornerArrow {K L : SSet.{u}} (j : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y) : Arrow SimplicialSpace.{u} :=
  Arrow.mk (ofSimplicialObject.map (coefficientCotensorPullback j p).π)

/-- A scalar cofibration and original global CSS fibration give the exact designated corner
fibration. -/
theorem designatedCotensorCorner_fibration {K L : SSet.{u}} (j : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y)
    (hj : cofibrations SSet.{u} j)
    (hp : RezkModel.modelCategory.categoryWithFibrations.fibrations p) :
    RezkModel.modelCategory.categoryWithFibrations.fibrations
      (designatedCotensorCornerArrow j p).hom := by
  let _ : ModelCategory (SimplicialPresheaf.{u} SimplexCategory) :=
    SimplicialPresheaf.InjectiveKan.originalLocalSmithModel SSet.Rezk.localizingMap.{u}
  have hp' := (coefficientFibration_iff p).mp hp
  have hq := SimplicialPresheaf.InjectiveKan.localized_cotensor_pullbackObjObj_fibration
    SSet.Rezk.localizingMap.{u} j p.hom (coefficientCotensorPullback j p) hj hp'
  exact (coefficientFibration_iff (designatedCotensorCornerArrow j p).hom).mpr hq

/-- Original global CSS triviality gives triviality of the same designated corner. -/
theorem designatedCotensorCorner_trivialFibration {K L : SSet.{u}} (j : K ⟶ L)
    {X Y : SimplicialSpace.{u}} (p : X ⟶ Y)
    (hj : cofibrations SSet.{u} j)
    (hp : (RezkModel.modelCategory.categoryWithFibrations.fibrations ⊓
      RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences) p) :
    (RezkModel.modelCategory.categoryWithFibrations.fibrations ⊓
      RezkModel.modelCategory.categoryWithWeakEquivalences.weakEquivalences)
      (designatedCotensorCornerArrow j p).hom := by
  let _ : ModelCategory (SimplicialPresheaf.{u} SimplexCategory) :=
    SimplicialPresheaf.InjectiveKan.originalLocalSmithModel SSet.Rezk.localizingMap.{u}
  have hp' := (coefficientTrivialFibration_iff p).mp hp
  have hq :=
      SimplicialPresheaf.InjectiveKan.localized_cotensor_pullbackObjObj_trivialFibration_of_right
    SSet.Rezk.localizingMap.{u} j p.hom (coefficientCotensorPullback j p) hj hp'
  exact (coefficientTrivialFibration_iff (designatedCotensorCornerArrow j p).hom).mpr hq

end SimplicialSpace.OriginalNamedCSSCotensor
