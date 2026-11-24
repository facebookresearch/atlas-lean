/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenExactFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationEverywhere

/-!
# Original simplex reindexing is Waldhausen exact

Every original simplex operator preserves the genuine successive-corner
stage cofibrations. Its selected intervals need not begin at zero: the
canonical arbitrary-row corner theorem supplies their actual pushout
witnesses, including equal endpoints. Pointwise evaluation of the original
whole stage pushout proves preservation of that pushout.

The result uses the named general stage structures and therefore applies
at each iteration of an arbitrary Waldhausen category.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original reindexed underlying stage diagram is precomposition. -/
theorem reindexStage_general_obj {a b : SimplexCategory} (α : a ⟶ b)
    (A : Stage C b.len) :
    ((reindexStage (C := C) α).obj A).obj = indexFunctor α ⋙ A.obj := rfl

/-- The actual reindexed stage map has its original selected component. -/
theorem reindexStage_general_app {a b : SimplexCategory} (α : a ⟶ b)
    {A B : Stage C b.len} (f : A ⟶ B) (x : Ar a.len) :
    ((reindexStage (C := C) α).map f).hom.app x =
      f.hom.app ((indexFunctor α).obj x) := rfl

/-- Every original simplex operator maps a zero stage to a zero stage. -/
theorem reindexStage_general_isZero {a b : SimplexCategory} (α : a ⟶ b)
    {A : Stage C b.len} (hA : IsZero A) :
    IsZero ((reindexStage (C := C) α).obj A) := by
  apply IsZero.of_full_of_faithful_of_isZero (forget C a.len)
  apply Functor.isZero
  intro x
  let Z : Stage C b.len := ⟨zeroDiagram C b.len, isStage_zeroDiagram C b.len⟩
  have hZ : IsZero Z := by
    apply IsZero.of_full_of_faithful_of_isZero (forget C b.len)
    exact Functor.isZero _ (fun _ => isZero_zero C)
  change IsZero (A.obj.obj ((indexFunctor α).obj x))
  exact (isZero_zero C).of_iso
    ((eval C b.len ((indexFunctor α).obj x)).mapIso (hA.iso hZ))

/-- Every whole original pushout along a genuine stage cofibration is
preserved by the original simplex operator. -/
theorem reindexStage_general_pushout {a b : SimplexCategory} (α : a ⟶ b)
    {A B A' P : Stage C b.len} (i : A ⟶ B) (f : A ⟶ A')
    (inl : A' ⟶ P) (inr : B ⟶ P) (hi : stageCofibrations C b.len i)
    (hP : IsPushout f i inl inr) :
    IsPushout ((reindexStage (C := C) α).map f) ((reindexStage (C := C) α).map i)
      ((reindexStage (C := C) α).map inl) ((reindexStage (C := C) α).map inr) := by
  apply IsPushout.of_map_of_faithful (forget C a.len)
  apply IsPushout.of_forall_isPushout_app
  intro x
  exact GeneralStagePushoutPresentation.isPushout_app (C := C) hi hP
    ((indexFunctor α).obj x)

/-- Original reindexing is exact for the genuine named general stage
structures, with all preservation fields earned from the original maps. -/
theorem reindexStage_general_isWaldhausenExact {a b : SimplexCategory} (α : a ⟶ b) :
    letI : HasZeroObject (Stage C a.len) := generalStageHasZeroObject C a.len
    letI : WaldhausenCategoryWithoutGluing (Stage C a.len) := generalStageWaldhausenCategory C a.len
    letI : HasZeroObject (Stage C b.len) := generalStageHasZeroObject C b.len
    letI : WaldhausenCategoryWithoutGluing (Stage C b.len) := generalStageWaldhausenCategory C b.len
    (reindexStage (C := C) α).IsWaldhausenExact := by
  let : HasZeroObject (Stage C a.len) := generalStageHasZeroObject C a.len
  let : WaldhausenCategoryWithoutGluing (Stage C a.len) := generalStageWaldhausenCategory C a.len
  let : HasZeroObject (Stage C b.len) := generalStageHasZeroObject C b.len
  let : WaldhausenCategoryWithoutGluing (Stage C b.len) := generalStageWaldhausenCategory C b.len
  constructor
  · intro A hA
    exact reindexStage_general_isZero C α hA
  · intro A B f hf
    exact (isCofibration_generalStageWaldhausenCategory_iff C a.len _).mpr
      (stageCofibrations_of_reindexStage C α f
        ((isCofibration_generalStageWaldhausenCategory_iff C b.len f).mp hf))
  · intro A B f hf
    exact (isWeakEquivalence_generalStageWaldhausenCategory_iff C a.len _).mpr
      (stageWeak_of_reindexStage C α f
        ((isWeakEquivalence_generalStageWaldhausenCategory_iff C b.len f).mp hf))
  · intro A B A' P i f inl inr hi hP
    exact reindexStage_general_pushout C α i f inl inr
      ((isCofibration_generalStageWaldhausenCategory_iff C b.len i).mp hi) hP

end CategoryTheory.Waldhausen.SConstruction
