/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenGeneral
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenFunctoriality
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationCorners

/-!
# Exactness of the original general finite-stage functor

An actual Waldhausen-exact functor preserves the original successive
pushout-corner cofibrations of S_n, and every whole stage pushout along
them. The named stage Waldhausen structures therefore make the original
stage functor exact. This supplies the categorical input to iterate the
original S-construction without assuming stage exactness.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uC vC uD vD

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.IsWaldhausenExact

open Waldhausen.SConstruction

variable {C : Type uC} [Category.{vC} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [WaldhausenCategoryWithoutGluing D]
variable {F : C ⥤ D} (hF : F.IsWaldhausenExact)

/-- The original exact functor maps each genuine successive stage
cofibration corner to its actual target pushout corner. -/
theorem mapStage_cofibrations (n : ℕ) {A B : Stage C n} (f : A ⟶ B)
    (hf : stageCofibrations C n f) :
    stageCofibrations D n ((hF.mapStage n).map f) := by
  intro i
  obtain ⟨P, inl, inr, d, hP, hl, hr, hd⟩ := hf i
  have hLeft : IsCofibration (A.zeroRowSuccMap i) :=
    (A.property.cofiber_triple (Fin.zero_le i.castSucc) i.castSucc_le_succ).1
  refine ⟨F.obj P, F.map inl, F.map inr, F.map d, ?_, ?_, ?_, hF.map_cofibration d hd⟩
  · exact (hF.map_pushout (A.zeroRowSuccMap i) (Stage.zeroRowApp f i.castSucc)
      inr inl hLeft hP.flip).flip
  · change F.map inl ≫ F.map d = F.map (Stage.zeroRowApp f i.succ)
    rw [← F.map_comp, hl]
  · change F.map inr ≫ F.map d = F.map (B.zeroRowSuccMap i)
    rw [← F.map_comp, hr]

/-- The image of an original zero stage is zero on every original
interval, hence zero in the actual full stage category. -/
theorem mapStage_isZero (n : ℕ) {A : Stage C n} (hA : IsZero A) :
    IsZero ((hF.mapStage n).obj A) := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
  apply IsZero.of_full_of_faithful_of_isZero (forget D n)
  apply Functor.isZero
  intro x
  have hAx : IsZero (A.obj.obj x) :=
    by
      let Z : Stage C n := ⟨zeroDiagram C n, isStage_zeroDiagram C n⟩
      have hZ : IsZero Z := by
        apply IsZero.of_full_of_faithful_of_isZero (forget C n)
        exact Functor.isZero _ (fun _ => isZero_zero C)
      exact (isZero_zero C).of_iso ((eval C n x).mapIso (hA.iso hZ))
  exact hF.map_isZero hAx

/-- Every original whole stage pushout along a genuine stage
cofibration is preserved by the actual stage functor. -/
theorem mapStage_pushout (n : ℕ) {A B A' P : Stage C n}
    (i : A ⟶ B) (f : A ⟶ A') (inl : A' ⟶ P) (inr : B ⟶ P)
    (hi : stageCofibrations C n i) (hP : IsPushout f i inl inr) :
    IsPushout ((hF.mapStage n).map f) ((hF.mapStage n).map i)
      ((hF.mapStage n).map inl) ((hF.mapStage n).map inr) := by
  apply IsPushout.of_map_of_faithful (forget D n)
  apply IsPushout.of_forall_isPushout_app
  intro x
  have hPx := GeneralStagePushoutPresentation.isPushout_app (C := C) hi hP x
  have hix : IsCofibration (i.hom.app x) :=
    by
      have hx : interval x.left x.right (leOfHom x.hom) = x := by
        rw [← Arrow.mk_eq x]
        exact congrArg Arrow.mk (Subsingleton.elim _ _)
      rw [← hx]
      exact Stage.intervalApp_isCofibration C i hi x.left x.right (leOfHom x.hom)
  exact hF.map_pushout (i.hom.app x) (f.hom.app x)
    (inl.hom.app x) (inr.hom.app x) hix hPx

/-- The original map on S_n is exact for the named genuine source
and target stage Waldhausen structures. -/
theorem mapStage_isWaldhausenExact (n : ℕ) :
    letI : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
    letI : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
    letI : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
    letI : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
    (hF.mapStage n).IsWaldhausenExact := by
  let : HasZeroObject (Stage C n) := generalStageHasZeroObject C n
  let : WaldhausenCategoryWithoutGluing (Stage C n) := generalStageWaldhausenCategory C n
  let : HasZeroObject (Stage D n) := generalStageHasZeroObject D n
  let : WaldhausenCategoryWithoutGluing (Stage D n) := generalStageWaldhausenCategory D n
  constructor
  · intro A hA
    exact hF.mapStage_isZero n hA
  · intro A B f hf
    exact (isCofibration_generalStageWaldhausenCategory_iff D n _).mpr
      (hF.mapStage_cofibrations n f
        ((isCofibration_generalStageWaldhausenCategory_iff C n f).mp hf))
  · intro A B f hf
    exact (isWeakEquivalence_generalStageWaldhausenCategory_iff D n _).mpr
      (hF.stageWeak_of_mapStage n f
        ((isWeakEquivalence_generalStageWaldhausenCategory_iff C n f).mp hf))
  · intro A B A' P i f inl inr hi hP
    exact hF.mapStage_pushout n i f inl inr
      ((isCofibration_generalStageWaldhausenCategory_iff C n i).mp hi) hP

end CategoryTheory.Functor.IsWaldhausenExact
