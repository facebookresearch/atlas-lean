/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FibrantCospanReplacement

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

section Packet

variable {D : WalkingCospan ⥤ C} (R S : FibrantCospanReplacement D)

example : WalkingCospan ⥤ C := R.P
example : D ⟶ R.P := R.unit
example : IsFibrant (R.P.obj WalkingCospan.one) := R.isFibrant_one
example : Fibration (R.P.map WalkingCospan.Hom.inl) := R.fibration_inl
example : Fibration (R.P.map WalkingCospan.Hom.inr) := R.fibration_inr
example (j : WalkingCospan) : trivialCofibrations C (R.unit.app j) :=
  R.unit_app_mem_trivialCofibrations j

example : FibrantCospanReplacement D where
  P := R.P
  unit := R.unit
  isFibrant_one := R.isFibrant_one
  fibration_inl := R.fibration_inl
  fibration_inr := R.fibration_inr
  unit_app_mem_trivialCofibrations := R.unit_app_mem_trivialCofibrations

example : R.pullbackObj = limit R.P := rfl

example : R.fromPullback = lim.map R.unit := rfl

example :
    R.fromPullback ≫ limit.π R.P WalkingCospan.left =
      limit.π D WalkingCospan.left ≫
        R.unit.app WalkingCospan.left := by
  apply FibrantCospanReplacement.fromPullback_inl

example :
    R.fromPullback ≫ limit.π R.P WalkingCospan.right =
      limit.π D WalkingCospan.right ≫
        R.unit.app WalkingCospan.right := by
  apply FibrantCospanReplacement.fromPullback_inr

example :
    ∃ f : S.pullbackObj ⟶ R.pullbackObj,
      WeakEquivalence f ∧ S.fromPullback ≫ f = R.fromPullback :=
  FibrantCospanReplacement.exists_weakEquivalence_pullbackObj R S

example :
    ∃ f : R.pullbackObj ⟶ R.pullbackObj,
      WeakEquivalence f ∧ R.fromPullback ≫ f = R.fromPullback :=
  FibrantCospanReplacement.exists_weakEquivalence_pullbackObj R R

example : WeakEquivalence R.fromPullback ↔ WeakEquivalence S.fromPullback :=
  FibrantCospanReplacement.weakEquivalence_fromPullback_iff R S

example (hR : WeakEquivalence R.fromPullback) : WeakEquivalence S.fromPullback :=
  (FibrantCospanReplacement.weakEquivalence_fromPullback_iff R S).mp hR

example (hS : WeakEquivalence S.fromPullback) : WeakEquivalence R.fromPullback :=
  (FibrantCospanReplacement.weakEquivalence_fromPullback_iff R S).mpr hS

example : True := by
  fail_if_success
    let _ := HomotopicalAlgebra.chosenFibrantCospanReplacement D
  fail_if_success
    let _ := FibrantCospanReplacement.replacementCospanLimitIso R.P
  fail_if_success
    let _ := FibrantCospanReplacement.replacementCospanLimit_isPullback R.P
  fail_if_success
    let _ := FibrantCospanReplacement.comparison R S
  fail_if_success
    let _ := FibrantCospanReplacement.canonicalComparison R S
  fail_if_success
    let _ := FibrantCospanReplacement.replacementIso R S
  fail_if_success
    let _ := FibrantCospanReplacement.localizationComparison R S
  fail_if_success
    let _ := FibrantCospanReplacement.hoUniversalProperty R
  fail_if_success
    have _ : R.pullbackObj = S.pullbackObj := rfl
  trivial

end Packet

example (D : WalkingCospan ⥤ C) : Nonempty (FibrantCospanReplacement D) :=
  FibrantCospanReplacement.nonempty D

#check FibrantCospanReplacement
#check FibrantCospanReplacement.nonempty
#check FibrantCospanReplacement.pullbackObj
#check FibrantCospanReplacement.fromPullback
#check FibrantCospanReplacement.fromPullback_inl
#check FibrantCospanReplacement.fromPullback_inr
#check FibrantCospanReplacement.exists_weakEquivalence_pullbackObj
#check FibrantCospanReplacement.weakEquivalence_fromPullback_iff
#check @FibrantCospanReplacement.{1, 1}
#check @FibrantCospanReplacement.{0, 0}

#print axioms FibrantCospanReplacement
#print axioms FibrantCospanReplacement.nonempty
#print axioms FibrantCospanReplacement.pullbackObj
#print axioms FibrantCospanReplacement.fromPullback
#print axioms FibrantCospanReplacement.fromPullback_inl
#print axioms FibrantCospanReplacement.fromPullback_inr
#print axioms FibrantCospanReplacement.exists_weakEquivalence_pullbackObj
#print axioms FibrantCospanReplacement.weakEquivalence_fromPullback_iff

end HomotopicalAlgebra
