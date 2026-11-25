/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.CartesianSM7
public import Mathlib.AlgebraicTopology.ModelCategory.IsCofibrant

/-!
# Closed symmetric monoidal model categories

This file records Hovey's pushout-product and unit axioms for an already
selected model structure and closed symmetric monoidal structure. It does not
install any of those parent structures.
-/

@[expose] public section

set_option autoImplicit false

universe v u

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra

variable (C : Type u) [Category.{v} C] [ModelCategory C]
  [MonoidalCategory C]

/-- A choice of cofibrant replacement of the tensor unit satisfying Hovey's
unit axiom. In a symmetric monoidal category, the displayed left tensor
condition also supplies its right tensor counterpart through the symmetry. -/
structure MonoidalUnitAxiomWitness where
  /-- The chosen cofibrant replacement of the tensor unit. -/
  Q : C
  /-- The replacement map to the tensor unit. -/
  q : Q ⟶ 𝟙_ C
  /-- The replacement object is cofibrant. -/
  Q_cofibrant : IsCofibrant Q
  /-- The replacement map is a trivial fibration. -/
  q_trivialFibration : trivialFibrations C q
  /-- Tensoring the replacement map with a cofibrant object is weak. -/
  tensor_weak : ∀ (X : C), IsCofibrant X →
    weakEquivalences C (q ▷ X)

/-- The pushout-product and unit axioms for the already selected model and
closed symmetric monoidal structures. -/
class IsClosedSymmetricMonoidalModelCategory
    [SymmetricCategory C] [MonoidalClosed C] : Prop where
  /-- The pushout-product of cofibrations is a cofibration. -/
  cofibration_pushoutProduct :
    PushoutProductLe (cofibrations C) (cofibrations C)
      (cofibrations C)
  /-- The pushout-product is trivial when its left factor is trivial. -/
  trivial_pushoutProduct_left :
    PushoutProductLe (trivialCofibrations C) (cofibrations C)
      (trivialCofibrations C)
  /-- The pushout-product is trivial when its right factor is trivial. -/
  trivial_pushoutProduct_right :
    PushoutProductLe (cofibrations C) (trivialCofibrations C)
      (trivialCofibrations C)
  /-- A Hovey unit-axiom witness; the tensor unit itself need not be
  cofibrant. -/
  unit_axiom : Nonempty (MonoidalUnitAxiomWitness C)

/-- When the tensor unit is cofibrant, its identity map is a unit-axiom
replacement, so the pushout-product clauses suffice. -/
theorem isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
    [SymmetricCategory C] [MonoidalClosed C] [IsCofibrant (𝟙_ C)]
    (cofibration_pushoutProduct :
      ∀ {A B K L : C} (i : A ⟶ B) (j : K ⟶ L),
        cofibrations C i → cofibrations C j →
          cofibrations C ((Arrow.mk i □ Arrow.mk j).hom))
    (trivial_pushoutProduct_left :
      ∀ {A B K L : C} (i : A ⟶ B) (j : K ⟶ L),
        trivialCofibrations C i → cofibrations C j →
          trivialCofibrations C ((Arrow.mk i □ Arrow.mk j).hom))
    (trivial_pushoutProduct_right :
      ∀ {A B K L : C} (i : A ⟶ B) (j : K ⟶ L),
        cofibrations C i → trivialCofibrations C j →
          trivialCofibrations C ((Arrow.mk i □ Arrow.mk j).hom)) :
    IsClosedSymmetricMonoidalModelCategory C where
  cofibration_pushoutProduct := by
    unfold PushoutProductLe
    intro A B K L i j hi hj
    exact cofibration_pushoutProduct i j hi hj
  trivial_pushoutProduct_left := by
    unfold PushoutProductLe
    intro A B K L i j hi hj
    exact trivial_pushoutProduct_left i j hi hj
  trivial_pushoutProduct_right := by
    unfold PushoutProductLe
    intro A B K L i j hi hj
    exact trivial_pushoutProduct_right i j hi hj
  unit_axiom := ⟨{
    Q := 𝟙_ C
    q := 𝟙 (𝟙_ C)
    Q_cofibrant := inferInstance
    q_trivialFibration := mem_trivialFibrations (𝟙 (𝟙_ C))
    tensor_weak := by
      intro X _
      rw [id_whiskerRight]
      exact mem_weakEquivalences (𝟙 ((𝟙_ C) ⊗ X)) }⟩

end HomotopicalAlgebra

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  [CartesianMonoidalCategory C] [SymmetricCategory C] [MonoidalClosed C]
  [IsClosedSymmetricMonoidalModelCategory C]

/-- A closed symmetric monoidal model category with cartesian tensor satisfies
the existing cartesian pushout-product axiom. -/
theorem IsClosedSymmetricMonoidalModelCategory.cartesianPushoutProductAxiom
    : CartesianPushoutProductAxiom (C := C) :=
  ⟨cofibration_pushoutProduct (C := C),
    trivial_pushoutProduct_left (C := C),
    trivial_pushoutProduct_right (C := C)⟩

/-- A closed symmetric monoidal model category with cartesian tensor satisfies
the pullback-Hom form of SM7. -/
theorem IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom
    : CartesianPullbackHomAxiom (C := C) :=
  cartesianPushoutProductAxiom_iff_pullbackHomAxiom.mp
    cartesianPushoutProductAxiom

end HomotopicalAlgebra
