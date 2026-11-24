/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Waldhausen.CofibrationArrow
public import MathlibExt.CategoryTheory.ExactCategory.Abelian
public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import Mathlib.Algebra.Category.Grp.Abelian

/-!
# Tests for Waldhausen cofibration arrows

The clients below pin the independent object/hom universes, full and faithful
forgetful functor, literal relative-latching orientation, closure API,
pointwise consequences, and named local zero-object installations.  A
concrete abelian-group square demonstrates that pointwise cofibration is
strictly weaker than relative cofibration.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory Limits ZeroObject
open CategoryTheory.ExactCategory
open CategoryTheory.Waldhausen

universe v u

namespace MathlibExtTest.CategoryTheory.Waldhausen
namespace CofibrationArrowTests

section Symbolic

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

example : Type (max u v) := CofibrationArrow C

example : (cofibrationArrowForget C).Full := inferInstance

example : (cofibrationArrowForget C).Faithful := inferInstance

example (X : CofibrationArrow C) : IsCofibration X.hom := X.prop

example {X Y : CofibrationArrow C} (α : X ⟶ Y) :
    α.left ≫ Y.hom = X.hom ≫ α.right :=
  MorphismProperty.Arrow.w α

example {X Y : CofibrationArrow C} (α : X ⟶ Y) :
    cofibrationArrowWeakEquivalences C α ↔
      IsWeakEquivalence α.left ∧ IsWeakEquivalence α.right :=
  Iff.rfl

example {X Y : CofibrationArrow C} {α : X ⟶ Y}
    (h : IsRelativeCofibration C α) :
    ∃ (P : C) (inB : X.right ⟶ P) (inA : Y.left ⟶ P)
      (d : P ⟶ Y.right),
      IsPushout X.hom α.left inB inA ∧
        inB ≫ d = α.right ∧
        inA ≫ d = Y.hom ∧ IsCofibration d :=
  h.2

example (X : CofibrationArrow C) :
    IsRelativeCofibration C (𝟙 X) :=
  IsRelativeCofibration.id C X

example {X Y Z : CofibrationArrow C} (α : X ⟶ Y) (β : Y ⟶ Z)
    (hα : IsRelativeCofibration C α)
    (hβ : IsRelativeCofibration C β) :
    IsRelativeCofibration C (α ≫ β) :=
  hα.comp C α β hβ

example {X Y : CofibrationArrow C} (α : X ⟶ Y) [IsIso α] :
    IsRelativeCofibration C α :=
  IsRelativeCofibration.of_isIso C α

example {X Y : CofibrationArrow C} {α : X ⟶ Y}
    (h : IsRelativeCofibration C α) :
    IsCofibration α.left ∧ IsCofibration α.right :=
  ⟨h.1, h.right C⟩

example {X Y : CofibrationArrow C} {α : X ⟶ Y}
    (h : IsRelativeCofibration C α) :
    arrowCofibrations C ((cofibrationArrowForget C).map α) :=
  h.pointwise C

example : IsZero (arrowZero C) := arrowZero_isZero C

example : IsZero (cofibrationArrowZero C) :=
  cofibrationArrowZero_isZero C

example :
    let _ : HasZeroObject (Arrow C) := arrowHasZeroObject C
    IsZero (0 : Arrow C) := by
  let _ : HasZeroObject (Arrow C) := arrowHasZeroObject C
  exact isZero_zero (Arrow C)

example :
    let _ : HasZeroObject (CofibrationArrow C) :=
      cofibrationArrowHasZeroObject C
    IsZero (0 : CofibrationArrow C) := by
  let _ : HasZeroObject (CofibrationArrow C) :=
    cofibrationArrowHasZeroObject C
  exact isZero_zero (CofibrationArrow C)

end Symbolic

section PointwiseIsNotRelative

local instance : WaldhausenCategoryWithoutGluing AddCommGrpCat.{0} :=
  ExactCategory.waldhausenCategory AddCommGrpCat.{0}

example :
    ∃ (X Y : CofibrationArrow AddCommGrpCat.{0}) (α : X ⟶ Y),
      arrowCofibrations AddCommGrpCat.{0}
          ((cofibrationArrowForget AddCommGrpCat.{0}).map α) ∧
        ¬ IsRelativeCofibration AddCommGrpCat.{0} α := by
  let K : AddCommGrpCat.{0} := AddCommGrpCat.of ℤ
  let X : CofibrationArrow AddCommGrpCat.{0} :=
    MorphismProperty.Arrow.mk (0 : (0 : AddCommGrpCat.{0}) ⟶ K)
      (WaldhausenCategoryWithoutGluing.zero_isCofibration K 0)
  let Y : CofibrationArrow AddCommGrpCat.{0} :=
    MorphismProperty.Arrow.mk (𝟙 K)
      ((WaldhausenCategoryWithoutGluing.cofibrations (C := AddCommGrpCat.{0})).id_mem K)
  let α : X ⟶ Y :=
    MorphismProperty.Arrow.homMk
      (0 : (0 : AddCommGrpCat.{0}) ⟶ K) (𝟙 K) (by
        dsimp [X, Y]
        rfl)
  refine ⟨X, Y, α, ?_, ?_⟩
  · exact ⟨WaldhausenCategoryWithoutGluing.zero_isCofibration K 0,
      (WaldhausenCategoryWithoutGluing.cofibrations
        (C := AddCommGrpCat.{0})).id_mem K⟩
  · intro h
    obtain ⟨_hleft, P, inB, inA, d, hpush, hinB, hinA, hd⟩ := h
    change IsAdmissibleMono d at hd
    let _ : Mono d := hd.mono
    have hright : α.right = Y.hom := by rfl
    have hinBd : inB ≫ d = inA ≫ d :=
      hinB.trans (hright.trans hinA.symm)
    have hin : inB = inA := (cancel_mono d).mp hinBd
    let q : P ⟶ K := hpush.desc (𝟙 K) 0 (by
      change (0 : (0 : AddCommGrpCat.{0}) ⟶ K) ≫ 𝟙 K =
        (0 : (0 : AddCommGrpCat.{0}) ⟶ K) ≫ (0 : K ⟶ K)
      simp)
    have hqB : inB ≫ q = 𝟙 K := hpush.inl_desc _ _ _
    have hqA : inA ≫ q = 0 := hpush.inr_desc _ _ _
    have hIdZero : (𝟙 K : K ⟶ K) = 0 := by
      rw [hin] at hqB
      exact hqB.symm.trans hqA
    have hOneZero : (1 : ℤ) = 0 := by
      simpa using congrArg
        (fun f : K ⟶ K ↦ f (1 : ℤ)) hIdZero
    exact one_ne_zero hOneZero

end PointwiseIsNotRelative

section InstanceAndScopeGuards

variable (C : Type u) [Category.{v} C] [HasZeroObject C]
  [WaldhausenCategoryWithoutGluing C]

#guard_msgs (error, substring := true) in
#synth HasZeroObject (Arrow C)

#guard_msgs (error, substring := true) in
#synth HasZeroObject (CofibrationArrow C)

#guard_msgs (error, substring := true) in
#synth WaldhausenCategoryWithoutGluing (Arrow C)

#guard_msgs (error, substring := true) in
#synth WaldhausenCategoryWithoutGluing (CofibrationArrow C)

#guard_msgs (error, substring := true) in
#check CategoryTheory.WaldhausenGluingAxiom

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.CylinderNormalization

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.arrowWaldhausenCategory

#guard_msgs (error, substring := true) in
#check CategoryTheory.Waldhausen.cylinderCofibrationFunctor

end InstanceAndScopeGuards

#print axioms CategoryTheory.Waldhausen.CofibrationArrow
#print axioms CategoryTheory.Waldhausen.IsRelativeCofibration
#print axioms CategoryTheory.Waldhausen.IsRelativeCofibration.comp
#print axioms CategoryTheory.Waldhausen.IsRelativeCofibration.of_isIso
#print axioms CategoryTheory.Waldhausen.IsRelativeCofibration.right
#print axioms CategoryTheory.Waldhausen.IsRelativeCofibration.pointwise
#print axioms CategoryTheory.Waldhausen.arrowZero_isZero
#print axioms CategoryTheory.Waldhausen.arrowHasZeroObject
#print axioms CategoryTheory.Waldhausen.cofibrationArrowZero_isZero
#print axioms CategoryTheory.Waldhausen.cofibrationArrowHasZeroObject

end CofibrationArrowTests
end MathlibExtTest.CategoryTheory.Waldhausen

end
