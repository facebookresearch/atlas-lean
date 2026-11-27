/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StagePushoutZeroRow

/-!
# Whole general finite-stage pushouts

The actual pointwise pushout has a genuine apex stage, all component
pushouts and a cobase leg satisfying the original stage cofibration
property. The whole functor-category universal property reflects through
the full stage inclusion. No caller apex or stage-pushout witness is used.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- An actual whole pushout along a genuine stage cofibration, retaining
all original component pushouts and the genuine stage cobase leg. -/
structure GeneralStagePushoutPresentation {n : ℕ} {A B D : Stage C n}
    (φ : A ⟶ B) (ψ : A ⟶ D) where
  /-- The actual apex finite stage. -/
  apex : Stage C n
  /-- The cobase leg from the second target stage. -/
  inl : D ⟶ apex
  /-- The other leg from the first target stage. -/
  inr : B ⟶ apex
  /-- The whole stage square is a pushout. -/
  isPushout : IsPushout ψ φ inl inr
  /-- Every original interval-component square is a pushout. -/
  appIsPushout : ∀ x : Ar n,
    IsPushout (ψ.hom.app x) (φ.hom.app x) (inl.hom.app x) (inr.hom.app x)
  /-- The actual cobase leg is a genuine stage cofibration. -/
  inlCofibration : stageCofibrations C n inl

namespace GeneralStagePushoutPresentation

variable {C} {n : ℕ} {A B D : Stage C n}

/-- Construct the whole stage pushout and its genuine cobase
cofibration from the original maps and stage-cofibration proof. -/
noncomputable def ofStageCofibration (φ : A ⟶ B) (ψ : A ⟶ D)
    (hφ : stageCofibrations C n φ) : GeneralStagePushoutPresentation C φ ψ := by
  let P := StagePointwisePushoutPresentation.ofStageCofibration (C := C) φ ψ hφ
  let apex : Stage C n := ⟨P.diagram, P.isStage hφ⟩
  let inl : D ⟶ apex := ⟨P.inl⟩
  let inr : B ⟶ apex := ⟨P.inr⟩
  have hPushout : IsPushout ψ φ inl inr := by
    apply IsPushout.of_map_of_faithful (forget C n)
    exact P.isPushout
  have hInl : stageCofibrations C n inl := by
    intro i
    exact P.inl_zeroRow_corner hφ i.castSucc_le_succ
  exact {
    apex := apex
    inl := inl
    inr := inr
    isPushout := hPushout
    appIsPushout := P.appIsPushout
    inlCofibration := hInl }

/-- Any actual stage pushout along a genuine stage cofibration is a
pushout at every original interval, by preservation of its actual span. -/
theorem isPushout_app {φ : A ⟶ B} {ψ : A ⟶ D}
    {P : Stage C n} {inl : D ⟶ P} {inr : B ⟶ P}
    (hφ : stageCofibrations C n φ) (hP : IsPushout ψ φ inl inr) (x : Ar n) :
    IsPushout (ψ.hom.app x) (φ.hom.app x) (inl.hom.app x) (inr.hom.app x) := by
  let Q := ofStageCofibration φ ψ hφ
  let : PreservesColimit (span ψ φ) (eval C n x) :=
    (Q.isPushout.preservesColimit_span_iff (F := eval C n x)).mpr (Q.appIsPushout x)
  exact hP.map (eval C n x)

end GeneralStagePushoutPresentation

end CategoryTheory.Waldhausen.SConstruction
