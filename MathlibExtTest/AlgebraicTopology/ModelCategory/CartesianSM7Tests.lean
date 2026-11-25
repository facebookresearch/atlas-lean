/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CartesianSM7

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u v₂ u₂

open CategoryTheory Limits
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped MonoidalCategory

namespace HomotopicalAlgebra.CartesianSM7Tests

#check PushoutProductLe
#check PullbackHomLe
#check pushoutProduct_le_llp_iff_pullbackHom_le_rlp
#check CartesianPushoutProductAxiom
#check CartesianPullbackHomAxiom
#check cartesianPushoutProductAxiom_iff_pullbackHomAxiom

section ArbitraryProperties

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [MonoidalCategory C] [MonoidalClosed C]
variable (P Q R : MorphismProperty C)

example (h : PushoutProductLe P Q R.llp) :
    PullbackHomLe P R Q.rlp :=
  (pushoutProduct_le_llp_iff_pullbackHom_le_rlp P Q R).mp h

example (h : PullbackHomLe P R Q.rlp) :
    PushoutProductLe P Q R.llp :=
  (pushoutProduct_le_llp_iff_pullbackHom_le_rlp P Q R).mpr h

example (_h : PushoutProductLe P Q R.llp) : True := by
  fail_if_success
    have _target : PullbackHomLe Q R P.rlp :=
      (pushoutProduct_le_llp_iff_pullbackHom_le_rlp Q P R).mp _h
  trivial

example (_h : PushoutProductLe P Q R.llp) : True := by
  fail_if_success
    have _target : PullbackHomLe P Q R.rlp :=
      (pushoutProduct_le_llp_iff_pullbackHom_le_rlp P Q R).mp _h
  trivial

end ArbitraryProperties

section ModelClauses

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [ModelCategory C]

example (h : CartesianPushoutProductAxiom (C := C)) :
    PushoutProductLe (cofibrations C) (cofibrations C)
      (cofibrations C) :=
  h.1

example (h : CartesianPushoutProductAxiom (C := C)) :
    PushoutProductLe (trivialCofibrations C) (cofibrations C)
      (trivialCofibrations C) :=
  h.2.1

example (h : CartesianPushoutProductAxiom (C := C)) :
    PushoutProductLe (cofibrations C) (trivialCofibrations C)
      (trivialCofibrations C) :=
  h.2.2

example
    (h₀ : PushoutProductLe (cofibrations C) (cofibrations C)
      (cofibrations C))
    (h₁ : PushoutProductLe (trivialCofibrations C) (cofibrations C)
      (trivialCofibrations C))
    (h₂ : PushoutProductLe (cofibrations C) (trivialCofibrations C)
      (trivialCofibrations C)) :
    CartesianPushoutProductAxiom (C := C) :=
  ⟨h₀, h₁, h₂⟩

example (h : CartesianPullbackHomAxiom (C := C)) :
    PullbackHomLe (cofibrations C) (trivialFibrations C)
      (trivialFibrations C) :=
  h.1

example (h : CartesianPullbackHomAxiom (C := C)) :
    PullbackHomLe (trivialCofibrations C) (fibrations C)
      (trivialFibrations C) :=
  h.2.1

example (h : CartesianPullbackHomAxiom (C := C)) :
    PullbackHomLe (cofibrations C) (fibrations C)
      (fibrations C) :=
  h.2.2

example
    (h₀ : PullbackHomLe (cofibrations C) (trivialFibrations C)
      (trivialFibrations C))
    (h₁ : PullbackHomLe (trivialCofibrations C) (fibrations C)
      (trivialFibrations C))
    (h₂ : PullbackHomLe (cofibrations C) (fibrations C)
      (fibrations C)) :
    CartesianPullbackHomAxiom (C := C) :=
  ⟨h₀, h₁, h₂⟩

example (h : CartesianPushoutProductAxiom (C := C)) :
    CartesianPullbackHomAxiom (C := C) :=
  cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mp h

example (h : CartesianPullbackHomAxiom (C := C)) :
    CartesianPushoutProductAxiom (C := C) :=
  cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mpr h

example
    (_h : PushoutProductLe (cofibrations C) (cofibrations C)
      (cofibrations C)) : True := by
  fail_if_success
    have _target : PushoutProductLe (trivialCofibrations C)
        (cofibrations C) (trivialCofibrations C) := _h
  trivial

example
    (_h : PushoutProductLe (cofibrations C) (cofibrations C)
      (cofibrations C)) : True := by
  fail_if_success
    have _target : PushoutProductLe (cofibrations C)
        (trivialCofibrations C) (trivialCofibrations C) := _h
  trivial

example (_h : CartesianPullbackHomAxiom (C := C)) : True := by
  fail_if_success
    have _target : PullbackHomLe (cofibrations C) (fibrations C)
        (trivialFibrations C) := _h.1
  trivial

end ModelClauses

section UniverseOne

variable {C : Type 1} [Category.{0} C]
variable [HasPushouts C] [HasPullbacks C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [ModelCategory C]

example (h : CartesianPushoutProductAxiom (C := C)) :
    CartesianPullbackHomAxiom (C := C) :=
  cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mp h

end UniverseOne

section UniverseZero

variable {C : Type} [Category C]
variable [HasPushouts C] [HasPullbacks C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [ModelCategory C]

example (h : CartesianPullbackHomAxiom (C := C)) :
    CartesianPushoutProductAxiom (C := C) :=
  cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mpr h

end UniverseZero

section Coexistence

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]
variable [ModelCategory C]
variable {D : Type u₂} [Category.{v₂} D]
variable [HasPushouts D] [HasPullbacks D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D]
variable [ModelCategory D]

example
    (hC : CartesianPushoutProductAxiom (C := C))
    (hD : CartesianPushoutProductAxiom (C := D)) :
    CartesianPullbackHomAxiom (C := C) ∧
      CartesianPullbackHomAxiom (C := D) :=
  ⟨cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mp hC,
    cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mp hD⟩

end Coexistence

section NoModelLeak

variable {C : Type u} [Category.{v} C]
variable [HasPushouts C] [HasPullbacks C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C]

example : True := by
  fail_if_success
    let _ := CartesianPushoutProductAxiom (C := C)
  trivial

example : True := by
  fail_if_success
    let _ := HomotopicalAlgebra.MonoidalUnitAxiomData
  trivial

end NoModelLeak

#print axioms pushoutProduct_le_llp_iff_pullbackHom_le_rlp
#print axioms cartesianPushoutProductAxiom_iff_pullbackHomAxiom

end HomotopicalAlgebra.CartesianSM7Tests
