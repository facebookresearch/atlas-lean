/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWaldhausenExactFunctor
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageOneEquivalence

/-!
# Original degree-one stage exactness for general Waldhausen categories

The original S1 evaluation reads the unique off-diagonal interval. The
actual successive corner condition is equivalent to a cofibration of
that original component. Zero objects and whole pushouts are reflected
by the original diagram inclusion and evaluated pointwise. This earns the
exact categorical S1 comparison needed for original suspension maps.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- The original degree-one successive corner has exactly the original
cofibration condition on the unique off-diagonal component. -/
theorem stageCofibrations_one_iff {A B : Stage C 1} (f : A ⟶ B) :
    stageCofibrations C 1 f ↔ IsCofibration (f.hom.app (interval (0 : Fin 2) 1 (by decide))) := by
  constructor
  · intro hf
    exact Stage.intervalApp_isCofibration C f hf 0 1 (by decide)
  · intro hf j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    let P := A.obj.obj (interval (0 : Fin 2) 1 (by decide))
    let inl : A.zeroRowObj (1 : Fin 2) ⟶ P := 𝟙 _
    let inr : B.zeroRowObj (0 : Fin 2) ⟶ P :=
      (B.property.diag_isZero 0).to_ P
    let d : P ⟶ B.zeroRowObj (1 : Fin 2) := f.hom.app (interval (0 : Fin 2) 1 (by decide))
    have hPush : IsPushout (A.zeroRowSuccMap 0) (Stage.zeroRowApp f (0 : Fin 2)) inl inr := by
      have hzA : IsZero (A.zeroRowObj (0 : Fin 2)) := A.property.diag_isZero 0
      have hzB : IsZero (B.zeroRowObj (0 : Fin 2)) := B.property.diag_isZero 0
      let : IsIso (Stage.zeroRowApp f (0 : Fin 2)) := IsZero.isIso hzA hzB _
      let : IsIso inl := by
        change IsIso (𝟙 P)
        exact (Iso.refl P).isIso_hom
      apply IsPushout.of_vert_isIso
      exact ⟨hzA.eq_of_src _ _⟩
    refine ⟨P, inl, inr, d, hPush, ?_, ?_, hf⟩
    · exact Category.id_comp _
    · exact (B.property.diag_isZero 0).eq_of_src _ _

/-- Original degree-one evaluation preserves the genuine stage cofibration. -/
theorem stageOneEval_general_cofibration {A B : Stage C 1} (f : A ⟶ B)
    (hf : stageCofibrations C 1 f) : IsCofibration ((stageOneEval C).map f) :=
  (stageCofibrations_one_iff C f).mp hf

/-- Original degree-one evaluation maps every zero stage to the original zero object. -/
theorem stageOneEval_general_isZero {A : Stage C 1} (hA : IsZero A) :
    IsZero ((stageOneEval C).obj A) := by
  let Z : Stage C 1 := ⟨zeroDiagram C 1, isStage_zeroDiagram C 1⟩
  have hZ : IsZero Z := by
    apply IsZero.of_full_of_faithful_of_isZero (forget C 1)
    exact Functor.isZero _ (fun _ => isZero_zero C)
  exact (isZero_zero C).of_iso ((stageOneEval C).mapIso (hA.iso hZ))

/-- Evaluation retains the actual unique off-diagonal pushout of the original whole stage. -/
theorem stageOneEval_general_pushout {A B A' P : Stage C 1}
    (i : A ⟶ B) (f : A ⟶ A') (inl : A' ⟶ P) (inr : B ⟶ P)
    (hi : stageCofibrations C 1 i) (hP : IsPushout f i inl inr) :
    IsPushout ((stageOneEval C).map f) ((stageOneEval C).map i)
      ((stageOneEval C).map inl) ((stageOneEval C).map inr) :=
  GeneralStagePushoutPresentation.isPushout_app (C := C) hi hP
    (interval (0 : Fin 2) 1 (by decide))

/-- The original degree-one evaluation is exact for the genuine general stage value. -/
theorem stageOneEval_general_isWaldhausenExact :
    letI : HasZeroObject (Stage C 1) := generalStageHasZeroObject C 1
    letI : WaldhausenCategoryWithoutGluing (Stage C 1) := generalStageWaldhausenCategory C 1
    (stageOneEval C).IsWaldhausenExact := by
  let : HasZeroObject (Stage C 1) := generalStageHasZeroObject C 1
  let : WaldhausenCategoryWithoutGluing (Stage C 1) := generalStageWaldhausenCategory C 1
  constructor
  · intro A hA
    exact stageOneEval_general_isZero C hA
  · intro A B f hf
    exact stageOneEval_general_cofibration C f
      ((isCofibration_generalStageWaldhausenCategory_iff C 1 f).mp hf)
  · intro A B f hf
    exact ((isWeakEquivalence_generalStageWaldhausenCategory_iff C 1 f).mp hf)
      (interval (0 : Fin 2) 1 (by decide))
  · intro A B A' P i f inl inr hi hP
    exact stageOneEval_general_pushout C i f inl inr
      ((isCofibration_generalStageWaldhausenCategory_iff C 1 i).mp hi) hP

/-- The original degree-one insertion sends original cofibrations to genuine stage corners. -/
theorem stageOne_general_cofibration {X Y : C} (f : X ⟶ Y) (hf : IsCofibration f) :
    stageCofibrations C 1 ((stageOne C).map f) := by
  apply (stageCofibrations_one_iff C _).mpr
  change (WaldhausenCategoryWithoutGluing.cofibrations (C := C))
    (((stageOne C).map f).hom.app (interval (0 : Fin 2) 1 (by decide)))
  simp only [stageOne_map_interval_zero_one]
  exact hf

/-- Original degree-one insertion retains zero on every original interval. -/
theorem stageOne_general_isZero {X : C} (hX : IsZero X) : IsZero ((stageOne C).obj X) := by
  apply IsZero.of_full_of_faithful_of_isZero (forget C 1)
  apply Functor.isZero
  intro a
  change IsZero (((stageOne C).obj X).obj.obj a)
  by_cases ha : a.left = a.right
  · rw [stageOne_obj_eq_zero_of_diag C X ha]
    exact isZero_zero C
  · rw [stageOne_obj_eq_X_of_offdiag C X ha]
    exact hX

/-- Original degree-one insertion preserves weak maps on every interval. -/
theorem stageOne_general_weak {X Y : C} (f : X ⟶ Y) (hf : IsWeakEquivalence f) :
    stageWeak C 1 ((stageOne C).map f) := by
  intro a
  change (WaldhausenCategoryWithoutGluing.weakEquivalences (C :=
    C)) (((stageOne C).map f).hom.app a)
  by_cases ha : a.left = a.right
  · have hzX : IsZero (((stageOne C).obj X).obj.obj a) := by
      rw [stageOne_obj_eq_zero_of_diag C X ha]
      exact isZero_zero C
    have hzY : IsZero (((stageOne C).obj Y).obj.obj a) := by
      rw [stageOne_obj_eq_zero_of_diag C Y ha]
      exact isZero_zero C
    let : IsIso (((stageOne C).map f).hom.app a) := IsZero.isIso hzX hzY _
    exact (WaldhausenCategoryWithoutGluing.weakEquivalences (C := C)).of_isIso _
  · have heq := ar1_eq_interval01_of_ne ha
    subst a
    simp only [stageOne_map_interval_zero_one]
    exact hf

/-- The original insertion carries every original cofibration pushout
to the actual whole stage pushout through the original S1 equivalence. -/
theorem stageOne_general_pushout {X Y X' P : C}
    (i : X ⟶ Y) (f : X ⟶ X') (inl : X' ⟶ P) (inr : Y ⟶ P)
    (hP : IsPushout f i inl inr) :
    IsPushout ((stageOne C).map f) ((stageOne C).map i)
      ((stageOne C).map inl) ((stageOne C).map inr) := by
  let : (stageOne C).IsEquivalence := (stageOneEquivalence C).isEquivalence_functor
  exact hP.map (stageOne C)

/-- The original degree-one insertion is exact for the genuine general stage value. -/
theorem stageOne_general_isWaldhausenExact :
    letI : HasZeroObject (Stage C 1) := generalStageHasZeroObject C 1
    letI : WaldhausenCategoryWithoutGluing (Stage C 1) := generalStageWaldhausenCategory C 1
    (stageOne C).IsWaldhausenExact := by
  let : HasZeroObject (Stage C 1) := generalStageHasZeroObject C 1
  let : WaldhausenCategoryWithoutGluing (Stage C 1) := generalStageWaldhausenCategory C 1
  constructor
  · intro X hX
    exact stageOne_general_isZero C hX
  · intro X Y f hf
    exact (isCofibration_generalStageWaldhausenCategory_iff C 1 _).mpr
      (stageOne_general_cofibration C f hf)
  · intro X Y f hf
    exact (isWeakEquivalence_generalStageWaldhausenCategory_iff C 1 _).mpr
      (stageOne_general_weak C f hf)
  · intro X Y X' P i f inl inr hi hP
    exact stageOne_general_pushout C i f inl inr hP

end CategoryTheory.Waldhausen.SConstruction
