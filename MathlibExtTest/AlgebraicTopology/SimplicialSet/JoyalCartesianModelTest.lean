/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalCartesianModel

/-!
# Joyal Cartesian Model Test
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

attribute [local instance] JoyalSSet.modelCategory

local instance : IsClosedSymmetricMonoidalModelCategory JoyalSSet.{u} :=
  JoyalSSet.isClosedSymmetricMonoidalModelCategory

/-- Cartesian and closed structures use the designated ordinary carrier. -/
example : CartesianMonoidalCategory JoyalSSet.{u} := inferInstance
example : MonoidalClosed JoyalSSet.{u} := inferInstance
example : SymmetricCategory JoyalSSet.{u} := inferInstance

/-- Both original cofibration inputs give a cofibration of the original whole corner. -/
example {A B K L : JoyalSSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    [Cofibration i] [Cofibration j] : Cofibration (Arrow.mk i □ Arrow.mk j).hom :=
  (cofibration_iff _).mpr
    (IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct (C := JoyalSSet.{u})
      i j ((cofibration_iff _).mp inferInstance) ((cofibration_iff _).mp inferInstance))

/-- Actual Joyal weakness on the left makes the original corner trivial. -/
example {A B K L : JoyalSSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    [Cofibration i] [WeakEquivalence i] [Cofibration j] :
    trivialCofibrations JoyalSSet.{u} (Arrow.mk i □ Arrow.mk j).hom :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left (C := JoyalSSet.{u})
    i j ((mem_trivialCofibrations_iff _).mpr ⟨inferInstance, inferInstance⟩)
      ((cofibration_iff _).mp inferInstance)

/-- The right weak-input law is independent of the left one. -/
example {A B K L : JoyalSSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    [Cofibration i] [Cofibration j] [WeakEquivalence j] :
    trivialCofibrations JoyalSSet.{u} (Arrow.mk i □ Arrow.mk j).hom :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right (C := JoyalSSet.{u})
    i j ((cofibration_iff _).mp inferInstance)
      ((mem_trivialCofibrations_iff _).mpr ⟨inferInstance, inferInstance⟩)

/-- The actual closed Cartesian axiom includes all three original pullback-Hom laws. -/
example : CartesianPullbackHomAxiom (C := JoyalSSet.{u}) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom

/-- A cofibration against an original trivial fibration gives a trivial relative Hom map. -/
example {A B X Y : JoyalSSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : cofibrations JoyalSSet.{u} i) (hp : trivialFibrations JoyalSSet.{u} p) :
    trivialFibrations JoyalSSet.{u} ((Opposite.op (Arrow.mk i) ⋔ Arrow.mk p).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom.1 i p hi hp

/-- A trivial cofibration against an arbitrary fibration gives a trivial relative Hom map. -/
example {A B X Y : JoyalSSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : trivialCofibrations JoyalSSet.{u} i) (hp : fibrations JoyalSSet.{u} p) :
    trivialFibrations JoyalSSet.{u} ((Opposite.op (Arrow.mk i) ⋔ Arrow.mk p).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom.2.1 i p hi hp

/-- Ordinary cofibration/fibration inputs give the genuine relative Joyal fibration. -/
example {A B X Y : JoyalSSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : cofibrations JoyalSSet.{u} i) (hp : fibrations JoyalSSet.{u} p) :
    fibrations JoyalSSet.{u} ((Opposite.op (Arrow.mk i) ⋔ Arrow.mk p).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom.2.2 i p hi hp

/-- The true Cartesian unit is cofibrant in the actual named model. -/
example : IsCofibrant (𝟙_ JoyalSSet.{u}) := JoyalSSet.tensorUnit_isCofibrant

/-- Its identity is a genuine unit-axiom replacement, with the original object and map. -/
example : ∃ w : MonoidalUnitAxiomWitness JoyalSSet.{u},
    w.Q = 𝟙_ JoyalSSet.{u} ∧ HEq w.q (𝟙 (𝟙_ JoyalSSet.{u})) := by
  let _ : IsCofibrant (𝟙_ JoyalSSet.{u}) := JoyalSSet.tensorUnit_isCofibrant
  refine ⟨{
    Q := 𝟙_ JoyalSSet.{u}
    q := 𝟙 (𝟙_ JoyalSSet.{u})
    Q_cofibrant := inferInstance
    q_trivialFibration := mem_trivialFibrations _
    tensor_weak := fun X _ => by
      rw [id_whiskerRight]
      exact mem_weakEquivalences _ }, rfl, ?_⟩
  rfl

/-- The original weak predicate in this instance is categorical equivalence. -/
example {X Y : JoyalSSet.{u}} (f : X ⟶ Y) :
    weakEquivalences JoyalSSet.{u} f ↔ SSet.categoricalEquivalences (JoyalSSet.forget.map f) := by
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences f ↔ _
  rw [JoyalSSet.modelCategory_weakEquivalences]
  rfl

/-- Higher value universes keep the same designated structures and actual named model. -/
example : letI : ModelCategory JoyalSSet.{u + 1} := JoyalSSet.modelCategory
    IsClosedSymmetricMonoidalModelCategory JoyalSSet.{u + 1} :=
  JoyalSSet.isClosedSymmetricMonoidalModelCategory
