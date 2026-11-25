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

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageCofibrationCorners
public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageZeroRowReconstruction
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Actual component pushouts for general stage cofibrations

Every interval component of a genuine stage cofibration is a base
cofibration. The base pushout axiom therefore gives each evaluated span a
colimit. The public pointwise functor-category colimit construction supplies
an actual raw apex diagram and both whole natural-transformation legs.

Only the C-independent interval normalization lemma is used from the
zero-row reconstruction API. No exact-category hypothesis enters a result.
-/

public section

open CategoryTheory Limits

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u) [Category.{v} C] [HasZeroObject C] [WaldhausenCategoryWithoutGluing C]

/-- Every original arrow-index component is a base cofibration, using
the canonical interval presentation of that same arrow object. -/
theorem Stage.app_isCofibration {n : ℕ} {A B : Stage C n}
    (φ : A ⟶ B) (hφ : stageCofibrations C n φ) (x : Ar n) :
    IsCofibration (φ.hom.app x) := by
  have h := Stage.intervalApp_isCofibration C φ hφ
    x.left x.right (leOfHom x.hom)
  exact Eq.mp (congrArg (fun y : Ar n => IsCofibration (φ.hom.app y))
    (interval_left_right_eq (n := n) x)) h

/-- A whole raw functor-category pushout of original stage maps, retaining
the actual apex diagram, legs and every component pushout. -/
structure StagePointwisePushoutPresentation {n : ℕ} {A B D : Stage C n}
    (φ : A ⟶ B) (ψ : A ⟶ D) where
  /-- The actual raw apex diagram. -/
  diagram : Ar n ⥤ C
  /-- The cobase leg from the second target diagram. -/
  inl : D.obj ⟶ diagram
  /-- The other leg from the first target diagram. -/
  inr : B.obj ⟶ diagram
  /-- The whole natural-transformation square is a pushout. -/
  isPushout : IsPushout ψ.hom φ.hom inl inr
  /-- Each original interval-component square is a pushout. -/
  appIsPushout : ∀ x : Ar n,
    IsPushout (ψ.hom.app x) (φ.hom.app x) (inl.app x) (inr.app x)

namespace StagePointwisePushoutPresentation

variable {C} {n : ℕ} {A B D : Stage C n} {φ : A ⟶ B} {ψ : A ⟶ D}

private theorem pointwiseHasColimit (φ : A ⟶ B) (ψ : A ⟶ D)
    (hφ : stageCofibrations C n φ) (x : Ar n) :
    HasColimit ((span ψ.hom φ.hom).flip.obj x) := by
  obtain ⟨P, inD, inB, hP, _⟩ :=
    WaldhausenCategoryWithoutGluing.cofibration_pushout (C := C) (φ.hom.app x)
      (Stage.app_isCofibration C φ hφ x) (D.obj.obj x) (ψ.hom.app x)
  have hspan :
      span (((evaluation (Ar n) C).obj x).map ψ.hom)
        (((evaluation (Ar n) C).obj x).map φ.hom) =
          span (ψ.hom.app x) (φ.hom.app x) := rfl
  let : HasColimit (span (((evaluation (Ar n) C).obj x).map ψ.hom)
      (((evaluation (Ar n) C).obj x).map φ.hom)) := by
    rw [hspan]
    exact hP.hasPushout
  exact hasColimit_of_iso
    (spanCompIso ((evaluation (Ar n) C).obj x) ψ.hom φ.hom)

/-- Construct the actual raw componentwise pushout from the original
stage cofibration, with no caller apex or colimit witness. -/
noncomputable def ofStageCofibration (φ : A ⟶ B) (ψ : A ⟶ D)
    (hφ : stageCofibrations C n φ) : StagePointwisePushoutPresentation C φ ψ := by
  letI : ∀ x : Ar n, HasColimit ((span ψ.hom φ.hom).flip.obj x) :=
    fun x => pointwiseHasColimit φ ψ hφ x
  letI : HasPushout ψ.hom φ.hom := inferInstance
  exact {
    diagram := pushout ψ.hom φ.hom
    inl := pushout.inl ψ.hom φ.hom
    inr := pushout.inr ψ.hom φ.hom
    isPushout := IsPushout.of_hasPushout ψ.hom φ.hom
    appIsPushout := fun x =>
      (IsPushout.of_hasPushout ψ.hom φ.hom).map ((evaluation (Ar n) C).obj x) }

/-- Every component of the actual raw cobase leg remains a base
cofibration, by the same original component pushout. -/
theorem inl_app_isCofibration (P : StagePointwisePushoutPresentation C φ ψ)
    (hφ : stageCofibrations C n φ) (x : Ar n) :
    IsCofibration (P.inl.app x) :=
  MorphismProperty.IsStableUnderCobaseChange.of_isPushout
    (P.appIsPushout x) (Stage.app_isCofibration C φ hφ x)

end StagePointwisePushoutPresentation

end CategoryTheory.Waldhausen.SConstruction
