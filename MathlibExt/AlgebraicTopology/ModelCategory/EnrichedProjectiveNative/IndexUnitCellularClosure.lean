/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.IndexUnitWeakCoefficientPropagation
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.StableCoproductClosure
import Mathlib.CategoryTheory.Retract
import MathlibExt.CategoryTheory.Limits.NaturalTransformationCoproductIso

/-!
# Actual source retracts and coproducts of the native index unit

The original source inclusion and retraction induce both components of the
unit-arrow retract. Naturality supplies both squares and functoriality supplies
both splitting equations, before any native index or coefficient is selected.
-/

set_option autoImplicit false
noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat
open HomotopicalAlgebra
open scoped CGWH.limits CGWH.modelCategory MonoidalClosed

namespace HomotopicalAlgebra.EnrichedProjective.Native.IndexUnitCellularClosure

open OperatorStabilizationK

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {A D L : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} D]

/-- Every complete source retract induces the actual retract of both native Kan-unit arrows. -/
def unitRetractArrow (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (r : Retract X Y) :
    RetractArrow ((leftKanRestrictionAdjunction j).unit.app X)
      ((leftKanRestrictionAdjunction j).unit.app Y) :=
  (leftKanRestrictionAdjunction j).unit.retractArrowApp r

/-- Both original source maps and their entire prolongation/restriction images are retained. -/
theorem unitRetractArrow_maps (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (r : Retract X Y) :
    (unitRetractArrow j r).i.left = r.i ∧
      (unitRetractArrow j r).i.right = (leftKan j ⋙ restriction j).map r.i ∧
      (unitRetractArrow j r).r.left = r.r ∧
      (unitRetractArrow j r).r.right = (leftKan j ⋙ restriction j).map r.r :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Naturality gives both actual unit squares and the same full retract gives both splits. -/
theorem unitRetractArrow_squares_and_splits (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (r : Retract X Y) :
    r.i ≫ (leftKanRestrictionAdjunction j).unit.app Y =
        (leftKanRestrictionAdjunction j).unit.app X ≫ (leftKan j ⋙ restriction j).map r.i ∧
      r.r ≫ (leftKanRestrictionAdjunction j).unit.app X =
        (leftKanRestrictionAdjunction j).unit.app Y ≫ (leftKan j ⋙ restriction j).map r.r ∧
      r.i ≫ r.r = 𝟙 X ∧
      (leftKan j ⋙ restriction j).map r.i ≫ (leftKan j ⋙ restriction j).map r.r =
        𝟙 ((leftKan j ⋙ restriction j).obj X) := by
  refine ⟨(leftKanRestrictionAdjunction j).unit.naturality r.i,
    (leftKanRestrictionAdjunction j).unit.naturality r.r, r.retract, ?_⟩
  rw [← CategoryTheory.Functor.map_comp, r.retract]
  exact (leftKan j ⋙ restriction j).map_id X

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- All original Omega tests of the unit descend along every actual source retract. -/
theorem unit_omegaTests_of_retract (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} A} (r : Retract X Y)
    (hY : NativeK.omegaTests s ((leftKanRestrictionAdjunction j).unit.app Y)) :
    NativeK.omegaTests s ((leftKanRestrictionAdjunction j).unit.app X) :=
  MorphismProperty.of_retract (unitRetractArrow j r) hY

end HomotopicalAlgebra.EnrichedProjective.Native.IndexUnitCellularClosure



namespace HomotopicalAlgebra.EnrichedProjective.Native.IndexUnitCellularClosure

open OperatorStabilizationK

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

variable {A D L : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  [EnrichedCategory PointedCGWH.{u, v} D]
  {J : Type w} [HasColimitsOfShape (Discrete J) (EnrichedFunctorCat PointedCGWH.{u, v} A)]

/-- Both genuine Kan adjunctions preserve the caller's complete coproduct, so its unit is the coproduct of units. -/
def unitCoproductArrowIso (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    (F : J → EnrichedFunctorCat PointedCGWH.{u, v} A) (c : Cofan F) (hc : IsColimit c) :
    Arrow.mk (Limits.Sigma.map (fun a => (leftKanRestrictionAdjunction j).unit.app (F a))) ≅
      Arrow.mk ((leftKanRestrictionAdjunction j).unit.app c.pt) := by
  let _ : PreservesColimitsOfSize.{w, w} (leftKan j) :=
    (leftKanRestrictionAdjunction j).leftAdjoint_preservesColimits
  let _ : PreservesColimitsOfSize.{w, w} (restriction j) :=
    (rightKanAdjunction j).leftAdjoint_preservesColimits
  let _ : PreservesColimitsOfShape (Discrete J) (leftKan j ⋙ restriction j) :=
    Limits.comp_preservesColimitsOfShape (F := leftKan j) (G := restriction j)
  exact NatTrans.coproductArrowIso (leftKanRestrictionAdjunction j).unit F c hc

variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual caller unit inherits the full Omega-test property of the same coproduct map of stage units. -/
theorem unit_omegaTests_of_coproductMap (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    (F : J → EnrichedFunctorCat PointedCGWH.{u, v} A) (c : Cofan F) (hc : IsColimit c)
    (h : NativeK.omegaTests s
      (Limits.Sigma.map (fun a => (leftKanRestrictionAdjunction j).unit.app (F a)))) :
    NativeK.omegaTests s ((leftKanRestrictionAdjunction j).unit.app c.pt) :=
  ((NativeK.omegaTests s).arrow_mk_iso_iff (unitCoproductArrowIso j F c hc)).mp h

/-- Stage-unit Omega tests give all tests of the same actual caller coproduct unit. -/
theorem unit_omegaTests_of_cofibrantCofan (s : NativeStabilizationFamily.{u, v} A L)
    (j : EnrichedFunctor PointedCGWH.{u, v} A D)
    [HasProductsOfShape J PointedCGWH.{u, v}]
    (F : J → EnrichedFunctorCat PointedCGWH.{u, v} A)
    [∀ a, IsCofibrant (F a)] [∀ a, IsCofibrant ((leftKan j ⋙ restriction j).obj (F a))]
    (c : Cofan F) (hc : IsColimit c)
    (h : ∀ a, NativeK.omegaTests s ((leftKanRestrictionAdjunction j).unit.app (F a))) :
    NativeK.omegaTests s ((leftKanRestrictionAdjunction j).unit.app c.pt) := by
  let _ : ∀ a, IsCofibrant ((𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} A)).obj (F a)) :=
    fun a => inferInstanceAs (IsCofibrant (F a))
  apply unit_omegaTests_of_coproductMap s j F c hc
  exact StableCoproductClosure.omegaTests_sigmaMap s
    (fun a => (leftKanRestrictionAdjunction j).unit.app (F a)) h

end HomotopicalAlgebra.EnrichedProjective.Native.IndexUnitCellularClosure
