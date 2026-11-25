/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantTensorPowers
public import MathlibExt.CategoryTheory.Monoidal.PushoutProductInitial

/-!
# The pushout-product part of the monoidal model axioms

The three pushout-product laws are recorded independently of a unit witness.
They concern the selected model structure and its actual tensor. Tensor
cofibrancy and preservation below use only these laws and the literal
initial-map pushout-product comparisons.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra

section RightTensorProperty

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [CategoryWithCofibrations C] [HasInitial C] [HasPushouts C]

/-- Right tensor by a cofibrant object preserves the specified map
property from its right-factor pushout-product law. Only the two actual
empty-diagram preservation hypotheses are required. -/
theorem whiskerRight_mem_of_isCofibrant
    (P : MorphismProperty C) [P.RespectsIso]
    (hPP : PushoutProductLe P (cofibrations C) P)
    {A B : C} (i : A ⟶ B) (K : C) [IsCofibrant K]
    [PreservesColimit (Functor.empty.{0} C) (tensorLeft A)]
    [PreservesColimit (Functor.empty.{0} C) (tensorLeft B)]
    (hi : P i) : P (i ▷ K) := by
  have hbox := hPP i (initial.to K) hi ((cofibration_iff _).mp inferInstance)
  exact (P.arrow_mk_iso_iff
    (MonoidalCategory.Arrow.PushoutProduct.isInitialRightIsoOfTensor
      (Arrow.mk i) initialIsInitial (K := K)
      (IsInitial.isInitialObj (tensorLeft A) (⊥_ C) initialIsInitial)
      (IsInitial.isInitialObj (tensorLeft B) (⊥_ C) initialIsInitial))).mp hbox

end RightTensorProperty

variable (C : Type u) [Category.{v} C] [ModelCategory C] [MonoidalCategory C]

/-- The pushout-product laws for a selected model structure, with no unit
axiom or tensor-unit cofibrancy included. -/
structure MonoidalPushoutProductAxiom : Prop where
  /-- Both cofibration factors give an actual tensor cofibration. -/
  cofibration_pushoutProduct :
    PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C)
  /-- A trivial left factor gives an actual tensor trivial cofibration. -/
  trivial_pushoutProduct_left :
    PushoutProductLe (trivialCofibrations C) (cofibrations C)
      (trivialCofibrations C)
  /-- A trivial right factor gives an actual tensor trivial cofibration. -/
  trivial_pushoutProduct_right :
    PushoutProductLe (cofibrations C) (trivialCofibrations C)
      (trivialCofibrations C)

variable {C}

/-- The full monoidal model axioms supply their pushout-product part. This
extraction does not select or compare a unit replacement. -/
theorem IsClosedSymmetricMonoidalModelCategory.pushoutProductAxiom
    [SymmetricCategory C] [MonoidalClosed C]
    [IsClosedSymmetricMonoidalModelCategory C] :
    MonoidalPushoutProductAxiom C where
  cofibration_pushoutProduct :=
    IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
  trivial_pushoutProduct_left :=
    IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
  trivial_pushoutProduct_right :=
    IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right

/-- In a braided category the actual whole-arrow pushout-product braiding
derives the right trivial branch from the left one. -/
theorem monoidalPushoutProductAxiom_of_left [BraidedCategory C]
    (hC : PushoutProductLe (cofibrations C) (cofibrations C) (cofibrations C))
    (hT : PushoutProductLe (trivialCofibrations C) (cofibrations C)
      (trivialCofibrations C)) :
    MonoidalPushoutProductAxiom C where
  cofibration_pushoutProduct := hC
  trivial_pushoutProduct_left := hT
  trivial_pushoutProduct_right := by
    intro A B K L i j hi hj
    exact ((trivialCofibrations C).arrow_mk_iso_iff
      (MonoidalCategory.Arrow.PushoutProduct.braiding (Arrow.mk j) (Arrow.mk i))).mp
      (hT j i hj hi)

namespace MonoidalPushoutProductAxiom

variable [BraidedCategory C] [MonoidalClosed C]
variable (hPP : MonoidalPushoutProductAxiom C)
include hPP

/-- Cofibrant objects have cofibrant tensor products before any unit axiom
has been verified. -/
theorem isCofibrant_tensorObj (X Y : C) [IsCofibrant X] [IsCofibrant Y] :
    IsCofibrant (X ⊗ Y) :=
  isCofibrant_tensorObj_of_pushoutProduct hPP.cofibration_pushoutProduct X Y

/-- Left tensor by a cofibrant object preserves actual cofibrations. -/
theorem whiskerLeft_mem_cofibrations
    (K : C) [IsCofibrant K] {A B : C} (i : A ⟶ B)
    (hi : cofibrations C i) : cofibrations C (K ◁ i) :=
  whiskerLeft_mem_of_isCofibrant (cofibrations C)
    hPP.cofibration_pushoutProduct K i hi

/-- Left tensor by a cofibrant object preserves actual trivial cofibrations. -/
theorem whiskerLeft_mem_trivialCofibrations
    (K : C) [IsCofibrant K] {A B : C} (i : A ⟶ B)
    (hi : trivialCofibrations C i) : trivialCofibrations C (K ◁ i) :=
  whiskerLeft_mem_of_isCofibrant (trivialCofibrations C)
    hPP.trivial_pushoutProduct_right K i hi

omit [BraidedCategory C] in
/-- Right tensor by a cofibrant object preserves actual cofibrations, using
the horizontal initial-map pushout and its whole Arrow isomorphism. -/
theorem whiskerRight_mem_cofibrations
    {A B : C} (i : A ⟶ B) (K : C) [IsCofibrant K]
    (hi : cofibrations C i) : cofibrations C (i ▷ K) :=
  whiskerRight_mem_of_isCofibrant (cofibrations C)
    hPP.cofibration_pushoutProduct i K hi

omit [BraidedCategory C] in
/-- Right tensor by a cofibrant object preserves actual trivial cofibrations
without introducing a unit witness. -/
theorem whiskerRight_mem_trivialCofibrations
    {A B : C} (i : A ⟶ B) (K : C) [IsCofibrant K]
    (hi : trivialCofibrations C i) : trivialCofibrations C (i ▷ K) :=
  whiskerRight_mem_of_isCofibrant (trivialCofibrations C)
    hPP.trivial_pushoutProduct_left i K hi

/-- Finite tensor powers use the separately stated true cofibrancy of the
unit for degree zero. -/
theorem isCofibrant_tensorPowObj
    (K : C) [IsCofibrant K] [IsCofibrant (𝟙_ C)] (r : ℕ) :
    IsCofibrant (TensorPower.tensorPowObj K r) := by
  let _ : ∀ n : ℕ, PreservesColimit (Functor.empty.{0} C)
      (tensorLeft (TensorPower.tensorPowObj K n)) := fun _ ↦ inferInstance
  exact isCofibrant_tensorPowObj_of_pushoutProduct hPP.cofibration_pushoutProduct K r

end MonoidalPushoutProductAxiom

end HomotopicalAlgebra
