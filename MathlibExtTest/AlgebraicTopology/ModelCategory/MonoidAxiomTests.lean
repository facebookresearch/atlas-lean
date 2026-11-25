/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.MonoidAxiom

/-! Tests for the generic monoid-axiom interface. -/

set_option autoImplicit false

universe w v u

open CategoryTheory MonoidalCategory
open CategoryTheory.MorphismProperty
open HomotopicalAlgebra
open scoped MonoidalCategory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.MonoidAxiomTests

#check @tensorTrivialCofibrationsRight
#check @whiskerRight_mem_tensorTrivialCofibrationsRight
#check @mem_tensorTrivialCofibrationsRight_iff
#check @tensorTrivialCofibrationsRight_le_iff
#check @MonoidAxiom

section Generic

variable (C : Type u) [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C] [SymmetricCategory C]

section LiteralGenerator

variable {A B : C} (f : A ⟶ B) (hf : trivialCofibrations C f)
  (X : C)

example : tensorTrivialCofibrationsRight C (f ▷ X) := by
  exact whiskerRight_mem_tensorTrivialCofibrationsRight C f hf X

example {M N : C} (g : M ⟶ N) :
    tensorTrivialCofibrationsRight C g ↔
      ∃ (X Y : C) (f : X ⟶ Y), trivialCofibrations C f ∧
        ∃ Z : C, Arrow.mk g = Arrow.mk (f ▷ Z) :=
  mem_tensorTrivialCofibrationsRight_iff C g

example (P : MorphismProperty C) :
    tensorTrivialCofibrationsRight C ≤ P ↔
      ∀ {A B : C} (f : A ⟶ B), trivialCofibrations C f →
        ∀ X : C, P (f ▷ X) :=
  tensorTrivialCofibrationsRight_le_iff C P

end LiteralGenerator

section Constructor

variable (h :
  transfiniteCompositions.{w}
    (coproducts.{w} (tensorTrivialCofibrationsRight C)).pushouts ≤
      weakEquivalences C)

example : MonoidAxiom.{w} C where
  cellularClosure_le_weakEquivalences := h

end Constructor

section Projection

variable [MonoidAxiom.{w} C]

example :
    transfiniteCompositions.{w}
      (coproducts.{w} (tensorTrivialCofibrationsRight C)).pushouts ≤
        weakEquivalences C :=
  MonoidAxiom.cellularClosure_le_weakEquivalences (C := C)

example (h₁ h₂ : MonoidAxiom.{w} C) : h₁ = h₂ :=
  Subsingleton.elim _ _

end Projection

section NoInstance

example : True := by
  fail_if_success
    let _ : MonoidAxiom.{w} C := inferInstance
  trivial

end NoInstance

end Generic

section UniverseClients

variable (C₁ : Type 1) [Category.{0} C₁] [ModelCategory C₁]
  [MonoidalCategory C₁] [SymmetricCategory C₁]

variable (C₀ : Type) [Category.{0} C₀] [ModelCategory C₀]
  [MonoidalCategory C₀] [SymmetricCategory C₀]

example : MorphismProperty C₁ := tensorTrivialCofibrationsRight C₁
example : Prop := MonoidAxiom.{1} C₁
example : MorphismProperty C₀ := tensorTrivialCofibrationsRight C₀
example : Prop := MonoidAxiom.{0} C₀

end UniverseClients

section Nonclaims

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.tensorTrivialCofibrationsLeft

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.MonoidAxiom.leftTensorClosure

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.HMonoidAxiom

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.FlatMonoidAxiom

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.localizedMonoidAxiom

#guard_msgs (error, substring := true) in
#check HomotopicalAlgebra.mappingSpectrum

end Nonclaims

#print axioms HomotopicalAlgebra.tensorTrivialCofibrationsRight
#print axioms
  HomotopicalAlgebra.whiskerRight_mem_tensorTrivialCofibrationsRight
#print axioms
  HomotopicalAlgebra.mem_tensorTrivialCofibrationsRight_iff
#print axioms
  HomotopicalAlgebra.tensorTrivialCofibrationsRight_le_iff
#print axioms HomotopicalAlgebra.MonoidAxiom

end MathlibExtTest.AlgebraicTopology.ModelCategory.MonoidAxiomTests
