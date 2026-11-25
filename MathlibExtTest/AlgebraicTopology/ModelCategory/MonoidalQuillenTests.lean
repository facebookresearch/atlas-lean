/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.MonoidalQuillen

/-!
# Tests for fixed-left tensor Quillen adjunctions

These clients pin the generic theorem, independent category universes, the
initial pushout-product comparison, both Quillen fields, and the ordered
right-trivial pushout-product clause.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped MonoidalCategory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.MonoidalQuillenTests

#check ihomAdjunction_isQuillenAdjunction_of_isCofibrant

section Generic

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

private noncomputable def initialPushoutProductIsoWitness
    (K : C) {A B : C} (j : A ⟶ B) :
    (Arrow.mk (initial.to K) □ Arrow.mk j) ≅ Arrow.mk (K ◁ j) := by
  let hA : IsInitial ((⊥_ C) ⊗ A) :=
    initialIsInitial.isInitialObj (tensorRight A)
  let hB : IsInitial ((⊥_ C) ⊗ B) :=
    initialIsInitial.isInitialObj (tensorRight B)
  let _ : IsIso ((⊥_ C) ◁ j) := isIso_of_isInitial hA hB _
  have hp : IsPushout (initial.to K ▷ A) ((⊥_ C) ◁ j)
      (𝟙 (K ⊗ A)) (hB.to (K ⊗ A)) :=
    .of_vert_isIso (sq := ⟨hA.hom_ext _ _⟩)
  set_option backward.defeqAttrib.useBackward true in
    set_option backward.isDefEq.respectTransparency false in
      exact Arrow.isoMk' _ _ hp.isoPushout.symm (Iso.refl _)
        (pushout.hom_ext (by simp) (hB.hom_ext _ _))

variable (K : C) [IsCofibrant K]

example : Adjunction.IsQuillenAdjunction (ihom.adjunction K) :=
  ihomAdjunction_isQuillenAdjunction_of_isCofibrant K

example : PreservesCofibrations (tensorLeft K) :=
  (ihomAdjunction_isQuillenAdjunction_of_isCofibrant K).preservesCofibrations

example : PreservesTrivialCofibrations (tensorLeft K) :=
  (ihomAdjunction_isQuillenAdjunction_of_isCofibrant K).preservesTrivialCofibrations

example (A : C) : (tensorRight A).IsLeftAdjoint := inferInstance

example {A B : C} (j : A ⟶ B) :
    IsIso (initialPushoutProductIsoWitness K j).hom.left := inferInstance

example {A B : C} (j : A ⟶ B) :
    pushout.inl (initial.to K ▷ A) ((⊥_ C) ◁ j) ≫
        (initialPushoutProductIsoWitness K j).hom.left =
      𝟙 (K ⊗ A) := by
  let hA : IsInitial ((⊥_ C) ⊗ A) :=
    initialIsInitial.isInitialObj (tensorRight A)
  let hB : IsInitial ((⊥_ C) ⊗ B) :=
    initialIsInitial.isInitialObj (tensorRight B)
  let _ : IsIso ((⊥_ C) ◁ j) := isIso_of_isInitial hA hB _
  have hp : IsPushout (initial.to K ▷ A) ((⊥_ C) ◁ j)
      (𝟙 (K ⊗ A)) (hB.to (K ⊗ A)) :=
    .of_vert_isIso (sq := ⟨hA.hom_ext _ _⟩)
  change pushout.inl _ _ ≫ hp.isoPushout.inv = 𝟙 (K ⊗ A)
  simp

example {A B : C} (j : A ⟶ B) :
    pushout.inr (initial.to K ▷ A) ((⊥_ C) ◁ j) ≫
        (initialPushoutProductIsoWitness K j).hom.left =
      (initialIsInitial.isInitialObj (tensorRight B)).to (K ⊗ A) := by
  let hA : IsInitial ((⊥_ C) ⊗ A) :=
    initialIsInitial.isInitialObj (tensorRight A)
  let hB : IsInitial ((⊥_ C) ⊗ B) :=
    initialIsInitial.isInitialObj (tensorRight B)
  let _ : IsIso ((⊥_ C) ◁ j) := isIso_of_isInitial hA hB _
  have hp : IsPushout (initial.to K ▷ A) ((⊥_ C) ◁ j)
      (𝟙 (K ⊗ A)) (hB.to (K ⊗ A)) :=
    .of_vert_isIso (sq := ⟨hA.hom_ext _ _⟩)
  change pushout.inr _ _ ≫ hp.isoPushout.inv = hB.to (K ⊗ A)
  simp

example {A B : C} (j : A ⟶ B) :
    (initialPushoutProductIsoWitness K j).hom.right = 𝟙 (K ⊗ B) := by
  rfl

example {A B : C} (j : A ⟶ B) :
    (initialPushoutProductIsoWitness K j).hom.left ≫ K ◁ j =
      (Arrow.mk (initial.to K) □ Arrow.mk j).hom ≫
        (initialPushoutProductIsoWitness K j).hom.right :=
  (initialPushoutProductIsoWitness K j).hom.w

example {A B : C} (j : A ⟶ B) (hj : cofibrations C j) :
    cofibrations C (K ◁ j) :=
  (ihomAdjunction_isQuillenAdjunction_of_isCofibrant K).preservesCofibrations
    j hj

example {A B : C} (j : A ⟶ B) (hj : trivialCofibrations C j) :
    trivialCofibrations C (K ◁ j) :=
  (ihomAdjunction_isQuillenAdjunction_of_isCofibrant K).preservesTrivialCofibrations
    j hj

example {A B : C} (j : A ⟶ B) (_hj : trivialCofibrations C j) : True := by
  fail_if_success
    let _wrong : trivialCofibrations C
        ((Arrow.mk (initial.to K) □ Arrow.mk j).hom) :=
      IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
        (initial.to K) j ((cofibration_iff _).mp inferInstance) _hj
  trivial

example {A B : C} (j : A ⟶ B) (_hj : trivialCofibrations C j) : True := by
  fail_if_success
    let _reversed : trivialCofibrations C
        ((Arrow.mk j □ Arrow.mk (initial.to K)).hom) :=
      IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
        j (initial.to K) ((cofibration_iff _).mp inferInstance) _hj
  trivial

end Generic

section UniverseZeroOne

variable {C : Type 1} [Category.{0} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
  (K : C) [IsCofibrant K]

example : Adjunction.IsQuillenAdjunction (ihom.adjunction K) :=
  ihomAdjunction_isQuillenAdjunction_of_isCofibrant K

end UniverseZeroOne

section UniverseOneZero

variable {C : Type} [Category.{1} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]
  (K : C) [IsCofibrant K]

example : Adjunction.IsQuillenAdjunction (ihom.adjunction K) :=
  ihomAdjunction_isQuillenAdjunction_of_isCofibrant K

end UniverseOneZero

#print axioms ihomAdjunction_isQuillenAdjunction_of_isCofibrant

end MathlibExtTest.AlgebraicTopology.ModelCategory.MonoidalQuillenTests
