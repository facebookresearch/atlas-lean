/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.Smith

/-!
# Tests for Smith recognition

These clients pin the result-free hypotheses, the extracted generating family,
both weak factorization systems, all three class equalities, the accessible
solution-set route, universe polymorphism and premise-deletion boundaries.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.SmithTests

#check SmithRecognitionInput
#check SmithModelStructureData
#check smithRecognition
#check smithRecognition_of_accessible

section GenericOutput

variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
  (I W : MorphismProperty C) [I.HasSmallObjectArgument.{w}]

example (h : SmithRecognitionInput.{w} (C := C) I W) :
    Nonempty (SmithModelStructureData.{w} (C := C) I W) :=
  smithRecognition I W h

variable (d : SmithModelStructureData.{w} (C := C) I W)

example : d.J.HasSmallObjectArgument.{w} := d.J_smallObject

example : d.J.rlp.llp = I.rlp.llp ⊓ W := d.trivialCofibrations_eq

example : d.J.rlp = (I.rlp.llp ⊓ W).rlp := d.fibrations_eq

example : d.J.rlp ⊓ W = I.rlp := d.trivialFibrations_eq

example : MorphismProperty.IsWeakFactorizationSystem I.rlp.llp I.rlp :=
  d.cofibration_wfs

example : MorphismProperty.IsWeakFactorizationSystem d.J.rlp.llp d.J.rlp :=
  d.trivialCofibration_wfs

example : True := by
  let _ : d.J.HasSmallObjectArgument.{w} := d.J_smallObject
  have : HasFunctorialFactorization d.J.rlp.llp d.J.rlp := inferInstance
  clear this
  trivial

example {X Y : C} (f : X ⟶ Y) (hf : d.J.rlp f) :
    (I.rlp.llp ⊓ W).rlp f := by
  rw [← d.fibrations_eq]
  exact hf

example {X Y : C} (f : X ⟶ Y) (hf : I.rlp f) :
    (d.J.rlp ⊓ W) f := by
  rw [d.trivialFibrations_eq]
  exact hf

end GenericOutput

section AccessibleRoute

variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
  (I W : MorphismProperty C) [I.HasSmallObjectArgument.{w}]
  [W.IsAccessible.{w}]
  (h₂ : W.HasTwoOutOfThreeProperty)
  (hR : W.IsStableUnderRetracts)
  (hI : I.rlp ≤ W)
  (hCobase : (I.rlp.llp ⊓ W).IsStableUnderCobaseChange)
  (hTrans : MorphismProperty.IsStableUnderTransfiniteComposition.{w}
    (I.rlp.llp ⊓ W))

example : Nonempty (SmithModelStructureData.{w} (C := C) I W) :=
  smithRecognition_of_accessible I W h₂ hR hI hCobase hTrans

example : ∃ (κ : Cardinal.{w}) (_ : Fact κ.IsRegular),
    W.IsCardinalAccessible κ :=
  MorphismProperty.IsAccessible.exists_cardinal W

end AccessibleRoute

section InputSurface

variable {C : Type u} [Category.{v} C]
  (I W : MorphismProperty C)
  (h₂ : W.HasTwoOutOfThreeProperty)
  (hR : W.IsStableUnderRetracts)
  (hI : I.rlp ≤ W)
  (hCobase : (I.rlp.llp ⊓ W).IsStableUnderCobaseChange)
  (hTrans : MorphismProperty.IsStableUnderTransfiniteComposition.{w}
    (I.rlp.llp ⊓ W))
  (hSol :
    ∀ {A B : C} (i : A ⟶ B), I i →
      ∃ (ι : Type w)
        (X : ι → W.arrowObjectProperty.FullSubcategory)
        (f : ∀ k, Arrow.mk i ⟶ W.arrowObjectProperty.ι.obj (X k)),
        ∀ (Y : W.arrowObjectProperty.FullSubcategory)
          (h : Arrow.mk i ⟶ W.arrowObjectProperty.ι.obj Y),
          ∃ (k : ι) (g : X k ⟶ Y),
            f k ≫ W.arrowObjectProperty.ι.map g = h)

example : SmithRecognitionInput.{w} (C := C) I W :=
  { weak_two_out_of_three := h₂
    weak_retracts := hR
    trivial_fibrations_weak := hI
    trivial_cofibrations_cobase := hCobase
    trivial_cofibrations_transfinite := hTrans
    solution_set := hSol }

example : True := by
  fail_if_success
    let _ : SmithRecognitionInput.{w} (C := C) I W :=
      { weak_two_out_of_three := h₂
        trivial_fibrations_weak := hI
        trivial_cofibrations_cobase := hCobase
        trivial_cofibrations_transfinite := hTrans
        solution_set := hSol }
  trivial

example : True := by
  fail_if_success
    let _ : SmithRecognitionInput.{w} (C := C) I W :=
      { weak_two_out_of_three := h₂
        weak_retracts := hR
        trivial_fibrations_weak := hI
        trivial_cofibrations_transfinite := hTrans
        solution_set := hSol }
  trivial

example : True := by
  fail_if_success
    let _ : SmithRecognitionInput.{w} (C := C) I W :=
      { weak_two_out_of_three := h₂
        weak_retracts := hR
        trivial_fibrations_weak := hI
        trivial_cofibrations_cobase := hCobase
        solution_set := hSol }
  trivial

example : True := by
  fail_if_success
    let _ : SmithRecognitionInput.{w} (C := C) I W :=
      { weak_two_out_of_three := h₂
        weak_retracts := hR
        trivial_fibrations_weak := hI
        trivial_cofibrations_cobase := hCobase
        trivial_cofibrations_transfinite := hTrans }
  trivial

example (_h : SmithRecognitionInput.{w} (C := C) I W) : True := by
  fail_if_success exact _h.J
  fail_if_success exact _h.cofibration_wfs
  fail_if_success exact _h.trivialCofibration_wfs
  fail_if_success exact _h.trivialCofibrations_eq
  fail_if_success exact _h.fibrations_eq
  fail_if_success exact _h.trivialFibrations_eq
  trivial

end InputSurface

section MissingSmallness

variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
  (I W : MorphismProperty C)
  (h : SmithRecognitionInput.{w} (C := C) I W)

example : True := by
  fail_if_success exact smithRecognition I W h
  trivial

end MissingSmallness

section MissingAccessibility

variable {C : Type u} [Category.{v} C] [IsLocallyPresentable.{w} C]
  (I W : MorphismProperty C) [I.HasSmallObjectArgument.{w}]
  (h₂ : W.HasTwoOutOfThreeProperty)
  (hR : W.IsStableUnderRetracts)
  (hI : I.rlp ≤ W)
  (hCobase : (I.rlp.llp ⊓ W).IsStableUnderCobaseChange)
  (hTrans : MorphismProperty.IsStableUnderTransfiniteComposition.{w}
    (I.rlp.llp ⊓ W))

example : True := by
  fail_if_success
    exact smithRecognition_of_accessible I W h₂ hR hI hCobase hTrans
  trivial

end MissingAccessibility

section ThirdEqualityDeletion

variable {C : Type u} [Category.{v} C]
  (I W J : MorphismProperty C)
  (hJ : J.HasSmallObjectArgument.{w})
  (hIWfs : MorphismProperty.IsWeakFactorizationSystem I.rlp.llp I.rlp)
  (hJWfs : MorphismProperty.IsWeakFactorizationSystem J.rlp.llp J.rlp)
  (hLeft : J.rlp.llp = I.rlp.llp ⊓ W)
  (hRight : J.rlp = (I.rlp.llp ⊓ W).rlp)

example : True := by
  fail_if_success
    let _ : SmithModelStructureData.{w} (C := C) I W :=
      { J := J
        J_smallObject := hJ
        cofibration_wfs := hIWfs
        trivialCofibration_wfs := hJWfs
        trivialCofibrations_eq := hLeft
        fibrations_eq := hRight }
  trivial

end ThirdEqualityDeletion

section ConcreteUniverses

#check @smithRecognition.{0, 0, 0}
#check @smithRecognition.{0, 0, 1}
#check @smithRecognition_of_accessible.{0, 0, 0}
#check @smithRecognition_of_accessible.{0, 0, 1}

end ConcreteUniverses

#print axioms SmithRecognitionInput
#print axioms SmithModelStructureData
#print axioms smithRecognition
#print axioms smithRecognition_of_accessible

end MathlibExtTest.AlgebraicTopology.ModelCategory.SmithTests
