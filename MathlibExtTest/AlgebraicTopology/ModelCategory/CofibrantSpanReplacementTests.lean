/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantSpanReplacement

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

section Packet

variable {D : WalkingSpan ⥤ C} (R S : CofibrantSpanReplacement D)

example : WalkingSpan ⥤ C := R.Q
example : R.Q ⟶ D := R.counit
example : IsCofibrant (R.Q.obj WalkingSpan.zero) := R.isCofibrant_zero
example : Cofibration (R.Q.map WalkingSpan.Hom.fst) := R.cofibration_fst
example : Cofibration (R.Q.map WalkingSpan.Hom.snd) := R.cofibration_snd
example (j : WalkingSpan) : trivialFibrations C (R.counit.app j) :=
  R.counit_app_mem_trivialFibrations j

example : CofibrantSpanReplacement D where
  Q := R.Q
  counit := R.counit
  isCofibrant_zero := R.isCofibrant_zero
  cofibration_fst := R.cofibration_fst
  cofibration_snd := R.cofibration_snd
  counit_app_mem_trivialFibrations := R.counit_app_mem_trivialFibrations

example : R.pushoutObj = colimit R.Q := rfl

example : R.toPushout = colim.map R.counit := rfl

example :
    colimit.ι R.Q WalkingSpan.left ≫ R.toPushout =
      R.counit.app WalkingSpan.left ≫ colimit.ι D WalkingSpan.left := by
  apply CofibrantSpanReplacement.inl_toPushout

example :
    colimit.ι R.Q WalkingSpan.right ≫ R.toPushout =
      R.counit.app WalkingSpan.right ≫ colimit.ι D WalkingSpan.right := by
  apply CofibrantSpanReplacement.inr_toPushout

example :
    ∃ f : R.pushoutObj ⟶ S.pushoutObj,
      WeakEquivalence f ∧ f ≫ S.toPushout = R.toPushout :=
  CofibrantSpanReplacement.exists_weakEquivalence_pushoutObj R S

example :
    ∃ f : R.pushoutObj ⟶ R.pushoutObj,
      WeakEquivalence f ∧ f ≫ R.toPushout = R.toPushout :=
  CofibrantSpanReplacement.exists_weakEquivalence_pushoutObj R R

example : WeakEquivalence R.toPushout ↔ WeakEquivalence S.toPushout :=
  CofibrantSpanReplacement.weakEquivalence_toPushout_iff R S

example (hR : WeakEquivalence R.toPushout) : WeakEquivalence S.toPushout :=
  (CofibrantSpanReplacement.weakEquivalence_toPushout_iff R S).mp hR

example (hS : WeakEquivalence S.toPushout) : WeakEquivalence R.toPushout :=
  (CofibrantSpanReplacement.weakEquivalence_toPushout_iff R S).mpr hS

example : True := by
  fail_if_success
    let _ := HomotopicalAlgebra.chosenCofibrantSpanReplacement D
  fail_if_success
    let _ := CofibrantSpanReplacement.replacementSpanColimitIso R.Q
  fail_if_success
    let _ := CofibrantSpanReplacement.Comparison R S
  fail_if_success
    let _ := CofibrantSpanReplacement.comparison R S
  fail_if_success
    let _ := CofibrantSpanReplacement.canonicalComparison R S
  fail_if_success
    let _ := CofibrantSpanReplacement.replacementIso R S
  fail_if_success
    let _ := CofibrantSpanReplacement.localizationComparison R S
  fail_if_success
    let _ := CofibrantSpanReplacement.hoUniversalProperty R
  fail_if_success
    have _ : R.pushoutObj = S.pushoutObj := rfl
  trivial

end Packet

example (D : WalkingSpan ⥤ C) : Nonempty (CofibrantSpanReplacement D) :=
  CofibrantSpanReplacement.nonempty D

#check CofibrantSpanReplacement
#check CofibrantSpanReplacement.nonempty
#check CofibrantSpanReplacement.pushoutObj
#check CofibrantSpanReplacement.toPushout
#check CofibrantSpanReplacement.inl_toPushout
#check CofibrantSpanReplacement.inr_toPushout
#check CofibrantSpanReplacement.exists_weakEquivalence_pushoutObj
#check CofibrantSpanReplacement.weakEquivalence_toPushout_iff

#print axioms CofibrantSpanReplacement
#print axioms CofibrantSpanReplacement.nonempty
#print axioms CofibrantSpanReplacement.pushoutObj
#print axioms CofibrantSpanReplacement.toPushout
#print axioms CofibrantSpanReplacement.inl_toPushout
#print axioms CofibrantSpanReplacement.inr_toPushout
#print axioms CofibrantSpanReplacement.exists_weakEquivalence_pushoutObj
#print axioms CofibrantSpanReplacement.weakEquivalence_toPushout_iff

end HomotopicalAlgebra
