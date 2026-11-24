/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.FiberedCategory.DiscreteFiber

/-!
# Tests for fibers over discrete targets

The tests exercise both comma-category orientations, their public object/map
computations, and the exact nonempty/connected criteria.  The two-point
example is load-bearing: essential surjectivity gives a nonempty fiber but
does not give connectedness, finality, or initiality.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe v₁ u₁ v₂ u₂

namespace MathlibExtTest.CategoryTheory.FiberedCategory.DiscreteFiberTests

section Generic

variable {A : Type u₁} [Category.{v₁} A]
variable {D : Type u₂} [Category.{v₂} D] [IsDiscrete D]
variable (F : A ⥤ D) (d : D)

example : F.Fiber d ≌ StructuredArrow d F :=
  F.fiberEquivalenceStructuredArrowOfIsDiscrete d

example : F.Fiber d ≌ CostructuredArrow F d :=
  F.fiberEquivalenceCostructuredArrowOfIsDiscrete d

example (X : F.Fiber d) :
    ((F.fiberEquivalenceStructuredArrowOfIsDiscrete d).functor.obj X).right = X.1 := by
  simp

example (X : F.Fiber d) :
    ((F.fiberEquivalenceStructuredArrowOfIsDiscrete d).functor.obj X).hom =
      eqToHom X.2.symm := by
  simp

example {X Y : F.Fiber d} (f : X ⟶ Y) :
    ((F.fiberEquivalenceStructuredArrowOfIsDiscrete d).functor.map f).right = f.1 := by
  simp

example (X : F.Fiber d) :
    ((F.fiberEquivalenceCostructuredArrowOfIsDiscrete d).functor.obj X).left = X.1 := by
  simp

example (X : F.Fiber d) :
    ((F.fiberEquivalenceCostructuredArrowOfIsDiscrete d).functor.obj X).hom =
      eqToHom X.2 := by
  simp

example {X Y : F.Fiber d} (f : X ⟶ Y) :
    ((F.fiberEquivalenceCostructuredArrowOfIsDiscrete d).functor.map f).left = f.1 := by
  simp

example : F.EssSurj ↔ ∀ x : D, Nonempty (F.Fiber x) :=
  F.essSurj_iff_forall_nonempty_fiber_of_isDiscrete

example : F.Final ↔ ∀ x : D, IsConnected (F.Fiber x) :=
  F.final_iff_forall_isConnected_fiber_of_isDiscrete

example : F.Initial ↔ ∀ x : D, IsConnected (F.Fiber x) :=
  F.initial_iff_forall_isConnected_fiber_of_isDiscrete

end Generic

section TwoPoints

/-- The unique functor from two discrete points to one discrete point. -/
def finTwoToPUnit : Discrete (Fin 2) ⥤ Discrete PUnit :=
  Discrete.functor (fun _ => Discrete.mk PUnit.unit)

/-- Either source point gives an object in the sole strict fiber. -/
def finTwoFiberObj (i : Fin 2) :
    finTwoToPUnit.Fiber (Discrete.mk PUnit.unit) :=
  ⟨Discrete.mk i, rfl⟩

example : Nonempty
    (finTwoToPUnit.Fiber (Discrete.mk PUnit.unit)) :=
  ⟨finTwoFiberObj 0⟩

/-- Essential surjectivity supplies the nonempty fiber. -/
theorem finTwoToPUnit_essSurj : finTwoToPUnit.EssSurj := by
  rw [finTwoToPUnit.essSurj_iff_forall_nonempty_fiber_of_isDiscrete]
  rintro ⟨x⟩
  obtain rfl := Subsingleton.elim x PUnit.unit
  exact ⟨finTwoFiberObj 0⟩

/-- The two objects in the strict fiber cannot be connected: every fiber
morphism has an underlying morphism in `Discrete (Fin 2)`, so it preserves the
source point. -/
theorem finTwoFiber_not_isConnected :
    ¬ IsConnected (finTwoToPUnit.Fiber (Discrete.mk PUnit.unit)) := by
  intro h
  let _ : IsConnected
      (finTwoToPUnit.Fiber (Discrete.mk PUnit.unit)) := h
  have hEq : (0 : Fin 2) = 1 :=
    constant_of_preserves_morphisms
      (fun X : finTwoToPUnit.Fiber (Discrete.mk PUnit.unit) => X.1.as)
      (fun _ _ f => Discrete.eq_of_hom (Functor.Fiber.fiberInclusion.map f))
      (finTwoFiberObj 0) (finTwoFiberObj 1)
  omega

example : ¬ finTwoToPUnit.Final := by
  intro h
  exact finTwoFiber_not_isConnected
    ((finTwoToPUnit.final_iff_forall_isConnected_fiber_of_isDiscrete.mp h)
      (Discrete.mk PUnit.unit))

example : ¬ finTwoToPUnit.Initial := by
  intro h
  exact finTwoFiber_not_isConnected
    ((finTwoToPUnit.initial_iff_forall_isConnected_fiber_of_isDiscrete.mp h)
      (Discrete.mk PUnit.unit))

/-! The criteria are theorems, not inferred global structure. -/

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth finTwoToPUnit.Final

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth finTwoToPUnit.Initial

/-- error: failed to synthesize -/
#guard_msgs (error, substring := true) in
#synth IsConnected (finTwoToPUnit.Fiber (Discrete.mk PUnit.unit))

end TwoPoints

section TypeZero

variable {A₀ : Type} [Category A₀]
variable {D₀ : Type} [Category D₀] [IsDiscrete D₀]

example (F : A₀ ⥤ D₀) (d : D₀) :
    F.Fiber d ≌ StructuredArrow d F :=
  F.fiberEquivalenceStructuredArrowOfIsDiscrete d

end TypeZero

section TypeOne

variable {A₁ : Type 1} [Category.{1} A₁]
variable {D₁ : Type 1} [Category.{1} D₁] [IsDiscrete D₁]

example (F : A₁ ⥤ D₁) (d : D₁) :
    F.Fiber d ≌ CostructuredArrow F d :=
  F.fiberEquivalenceCostructuredArrowOfIsDiscrete d

end TypeOne

section MixedUniversesForward

variable {A₀ : Type} [Category.{1} A₀]
variable {D₁ : Type 1} [Category.{0} D₁] [IsDiscrete D₁]

example (F : A₀ ⥤ D₁) (d : D₁) :
    F.Fiber d ≌ StructuredArrow d F :=
  F.fiberEquivalenceStructuredArrowOfIsDiscrete d

example (F : A₀ ⥤ D₁) :
    F.EssSurj ↔ ∀ d : D₁, Nonempty (F.Fiber d) :=
  F.essSurj_iff_forall_nonempty_fiber_of_isDiscrete

end MixedUniversesForward

section MixedUniversesReverse

variable {A₁ : Type 1} [Category.{0} A₁]
variable {D₀ : Type} [Category.{1} D₀] [IsDiscrete D₀]

example (F : A₁ ⥤ D₀) (d : D₀) :
    F.Fiber d ≌ CostructuredArrow F d :=
  F.fiberEquivalenceCostructuredArrowOfIsDiscrete d

example (F : A₁ ⥤ D₀) :
    F.Final ↔ ∀ d : D₀, IsConnected (F.Fiber d) :=
  F.final_iff_forall_isConnected_fiber_of_isDiscrete

end MixedUniversesReverse

end MathlibExtTest.CategoryTheory.FiberedCategory.DiscreteFiberTests

end
