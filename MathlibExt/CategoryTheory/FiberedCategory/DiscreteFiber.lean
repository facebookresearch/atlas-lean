/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.FiberedCategory.FiberToStructuredArrow
public import Mathlib.CategoryTheory.Discrete.Basic
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Limits.Final

/-!
# Fibers of functors into discrete categories

For a functor `F : A ⥤ D` with discrete target, its strict fiber over `d : D`
is equivalent to both comma categories used by categorical finality:

* `StructuredArrow d F`, whose arrows point `d ⟶ F.obj a`; and
* `CostructuredArrow F d`, whose arrows point `F.obj a ⟶ d`.

Consequently essential surjectivity is exactly nonemptiness of every strict
fiber, while finality and initiality are exactly connectedness of every strict
fiber.  These are theorem-valued criteria; this file installs no global
essential-surjectivity, finality, initiality, or connectedness instance and
makes no contractibility, homotopy-finality, nerve, realization, or weak-
equivalence claim.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {D : Type u₂} [Category.{v₂} D] [IsDiscrete D]

/-- For a discrete target, the strict fiber over `d` is equivalent to the
structured-arrow category `d ↓ F`. -/
def fiberEquivalenceStructuredArrowOfIsDiscrete (F : A ⥤ D) (d : D) :
    F.Fiber d ≌ StructuredArrow d F := by
  let G := fiberToStructuredArrow (p := F) d
  letI : G.Faithful :=
    { map_injective := fun {X Y} f g h => by
        apply Fiber.hom_ext
        exact congrArg StructuredArrow.Hom.right h }
  letI : G.Full :=
    ⟨fun {X Y} f => by
      let hf : F.IsHomLift (𝟙 d) f.right :=
        IsHomLift.of_commsq F (𝟙 d) f.right X.2 Y.2
          (Subsingleton.elim _ _)
      exact ⟨⟨f.right, hf⟩, by
        apply StructuredArrow.hom_ext
        rfl⟩⟩
  letI : G.EssSurj :=
    ⟨fun Y => by
      let X : F.Fiber d :=
        ⟨Y.right, (IsDiscrete.eq_of_hom Y.hom).symm⟩
      exact ⟨X, ⟨StructuredArrow.isoMk (Iso.refl _)
        (Subsingleton.elim _ _)⟩⟩⟩
  letI : G.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact G.asEquivalence

/-- Compatibility functor of the existing discrete fiber equivalence.
The general inclusion is `Functor.fiberToStructuredArrow`; this declaration
retains the original discrete API and uses that same functor. -/
def fiberToStructuredArrowOfIsDiscrete (F : A ⥤ D) (d : D) :
    F.Fiber d ⥤ StructuredArrow d F :=
  (fiberEquivalenceStructuredArrowOfIsDiscrete F d).functor

@[simp]
theorem fiberToStructuredArrowOfIsDiscrete_obj_right
    (F : A ⥤ D) (d : D) (X : F.Fiber d) :
    ((fiberToStructuredArrowOfIsDiscrete F d).obj X).right = X.1 :=
  rfl

@[simp]
theorem fiberToStructuredArrowOfIsDiscrete_obj_hom
    (F : A ⥤ D) (d : D) (X : F.Fiber d) :
    ((fiberToStructuredArrowOfIsDiscrete F d).obj X).hom =
      eqToHom X.2.symm :=
  rfl

@[simp]
theorem fiberToStructuredArrowOfIsDiscrete_map_right
    (F : A ⥤ D) (d : D) {X Y : F.Fiber d} (f : X ⟶ Y) :
    ((fiberToStructuredArrowOfIsDiscrete F d).map f).right = f.1 :=
  rfl

@[simp]
theorem fiberEquivalenceStructuredArrowOfIsDiscrete_functor_obj_right
    (F : A ⥤ D) (d : D) (X : F.Fiber d) :
    ((fiberEquivalenceStructuredArrowOfIsDiscrete F d).functor.obj X).right = X.1 :=
  rfl

@[simp]
theorem fiberEquivalenceStructuredArrowOfIsDiscrete_functor_obj_hom
    (F : A ⥤ D) (d : D) (X : F.Fiber d) :
    ((fiberEquivalenceStructuredArrowOfIsDiscrete F d).functor.obj X).hom =
      eqToHom X.2.symm :=
  rfl

@[simp]
theorem fiberEquivalenceStructuredArrowOfIsDiscrete_functor_map_right
    (F : A ⥤ D) (d : D) {X Y : F.Fiber d} (f : X ⟶ Y) :
    ((fiberEquivalenceStructuredArrowOfIsDiscrete F d).functor.map f).right = f.1 :=
  rfl

/-- The strict fiber maps to the costructured-arrow category over the same
object.  The fiber equality gives the arrow `F.obj a ⟶ d` in its stored
orientation. -/
def fiberToCostructuredArrowOfIsDiscrete (F : A ⥤ D) (d : D) :
    F.Fiber d ⥤ CostructuredArrow F d where
  obj X := CostructuredArrow.mk (eqToHom X.2)
  map {X Y} f := CostructuredArrow.homMk f.1 (Subsingleton.elim _ _)
  map_id X := by
    apply CostructuredArrow.hom_ext
    rfl
  map_comp f g := by
    apply CostructuredArrow.hom_ext
    rfl

@[simp]
theorem fiberToCostructuredArrowOfIsDiscrete_obj_left
    (F : A ⥤ D) (d : D) (X : F.Fiber d) :
    ((fiberToCostructuredArrowOfIsDiscrete F d).obj X).left = X.1 :=
  rfl

@[simp]
theorem fiberToCostructuredArrowOfIsDiscrete_obj_hom
    (F : A ⥤ D) (d : D) (X : F.Fiber d) :
    ((fiberToCostructuredArrowOfIsDiscrete F d).obj X).hom =
      eqToHom X.2 :=
  rfl

@[simp]
theorem fiberToCostructuredArrowOfIsDiscrete_map_left
    (F : A ⥤ D) (d : D) {X Y : F.Fiber d} (f : X ⟶ Y) :
    ((fiberToCostructuredArrowOfIsDiscrete F d).map f).left = f.1 :=
  rfl

/-- For a discrete target, the strict fiber over `d` is equivalent to the
costructured-arrow category `F ↓ d`. -/
def fiberEquivalenceCostructuredArrowOfIsDiscrete (F : A ⥤ D) (d : D) :
    F.Fiber d ≌ CostructuredArrow F d := by
  let G := fiberToCostructuredArrowOfIsDiscrete F d
  letI : G.Faithful :=
    { map_injective := fun {X Y} f g h => by
        apply Fiber.hom_ext
        exact congrArg CostructuredArrow.Hom.left h }
  letI : G.Full :=
    ⟨fun {X Y} f => by
      let hf : F.IsHomLift (𝟙 d) f.left :=
        IsHomLift.of_commsq F (𝟙 d) f.left X.2 Y.2
          (Subsingleton.elim _ _)
      exact ⟨⟨f.left, hf⟩, by
        apply CostructuredArrow.hom_ext
        rfl⟩⟩
  letI : G.EssSurj :=
    ⟨fun Y => by
      let X : F.Fiber d := ⟨Y.left, IsDiscrete.eq_of_hom Y.hom⟩
      exact ⟨X, ⟨CostructuredArrow.isoMk (Iso.refl _)
        (Subsingleton.elim _ _)⟩⟩⟩
  letI : G.IsEquivalence :=
    { faithful := inferInstance
      full := inferInstance
      essSurj := inferInstance }
  exact G.asEquivalence

@[simp]
theorem fiberEquivalenceCostructuredArrowOfIsDiscrete_functor_obj_left
    (F : A ⥤ D) (d : D) (X : F.Fiber d) :
    ((fiberEquivalenceCostructuredArrowOfIsDiscrete F d).functor.obj X).left = X.1 :=
  rfl

@[simp]
theorem fiberEquivalenceCostructuredArrowOfIsDiscrete_functor_obj_hom
    (F : A ⥤ D) (d : D) (X : F.Fiber d) :
    ((fiberEquivalenceCostructuredArrowOfIsDiscrete F d).functor.obj X).hom =
      eqToHom X.2 :=
  rfl

@[simp]
theorem fiberEquivalenceCostructuredArrowOfIsDiscrete_functor_map_left
    (F : A ⥤ D) (d : D) {X Y : F.Fiber d} (f : X ⟶ Y) :
    ((fiberEquivalenceCostructuredArrowOfIsDiscrete F d).functor.map f).left = f.1 :=
  rfl

/-- A functor into a discrete category is essentially surjective exactly when
every strict fiber is nonempty. -/
theorem essSurj_iff_forall_nonempty_fiber_of_isDiscrete (F : A ⥤ D) :
    F.EssSurj ↔ ∀ d : D, Nonempty (F.Fiber d) := by
  constructor
  · intro h d
    obtain ⟨X, ⟨e⟩⟩ := h.mem_essImage d
    exact ⟨⟨X, IsDiscrete.eq_of_hom e.hom⟩⟩
  · intro h
    apply essSurj_of_surj
    intro d
    obtain ⟨X⟩ := h d
    exact ⟨X.1, X.2⟩

/-- A functor into a discrete category is final exactly when every strict
fiber is connected.  The structured-arrow orientation is `d ⟶ F.obj a`. -/
theorem final_iff_forall_isConnected_fiber_of_isDiscrete (F : A ⥤ D) :
    F.Final ↔ ∀ d : D, IsConnected (F.Fiber d) := by
  constructor
  · intro h d
    exact (isConnected_iff_of_equivalence
      (fiberEquivalenceStructuredArrowOfIsDiscrete F d)).mpr (h.out d)
  · intro h
    exact ⟨fun d => (isConnected_iff_of_equivalence
      (fiberEquivalenceStructuredArrowOfIsDiscrete F d)).mp (h d)⟩

/-- A functor into a discrete category is initial exactly when every strict
fiber is connected.  The costructured-arrow orientation is `F.obj a ⟶ d`. -/
theorem initial_iff_forall_isConnected_fiber_of_isDiscrete (F : A ⥤ D) :
    F.Initial ↔ ∀ d : D, IsConnected (F.Fiber d) := by
  constructor
  · intro h d
    exact (isConnected_iff_of_equivalence
      (fiberEquivalenceCostructuredArrowOfIsDiscrete F d)).mpr (h.out d)
  · intro h
    exact ⟨fun d => (isConnected_iff_of_equivalence
      (fiberEquivalenceCostructuredArrowOfIsDiscrete F d)).mp (h d)⟩

end CategoryTheory.Functor

end
