/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Actual relative words over an original category

A word is a finite string of new arrows separated by actual original
Hom segments. Original identity segments and loop arrows remain literal.
Composition concatenates the strings and composes only adjacent original
segments. The object type and original category are retained, with
independent original object, original Hom and new-arrow universes.
-/

universe u v w
open CategoryTheory

namespace CategoryTheory.RelativeWords

variable {C : Type u} [Category.{v} C] (G : C → C → Type w)

/-- A finite original Hom string whose supplied new arrows remain individually represented. -/
inductive Word : C → C → Type (max u v w)
  | old {a b : C} (f : a ⟶ b) : Word a b
  | cons {a x y b : C} (f : a ⟶ x) (g : G x y) (p : Word y b) : Word a b

namespace Word

variable {G} {a b c d : C}

/-- Precompose the first original segment, keeping every supplied new arrow. -/
def precompose (f : a ⟶ b) : Word G b c → Word G a c
  | .old g => .old (f ≫ g)
  | .cons g e p => .cons (f ≫ g) e p

/-- Concatenate whole relative words and compose their adjacent original segments. -/
def comp : {a b c : C} → Word G a b → Word G b c → Word G a c
  | _, _, _, .old f, q => precompose f q
  | _, _, _, .cons f e p, q => .cons f e (comp p q)

/-- The actual number of supplied new arrows in the whole original word. -/
def length : {a b : C} → Word G a b → ℕ
  | _, _, .old _ => 0
  | _, _, .cons _ _ p => p.length + 1

/-- Original precomposition keeps the whole new-arrow count. -/
theorem length_precompose (f : a ⟶ b) (p : Word G b c) :
    (precompose f p).length = p.length := by cases p <;> rfl

/-- Original identity segments compose as their same identity. -/
theorem precompose_id (p : Word G a b) : precompose (𝟙 a) p = p := by
  cases p <;> simp only [precompose, Category.id_comp]

/-- Consecutive original precomposition is actual original composition. -/
theorem precompose_precompose (f : a ⟶ b) (g : b ⟶ c) (p : Word G c d) :
    precompose f (precompose g p) = precompose (f ≫ g) p := by
  cases p <;> simp only [precompose, Category.assoc]

/-- Original precomposition commutes with concatenation of whole relative words. -/
theorem precompose_comp (f : a ⟶ b) (p : Word G b c) (q : Word G c d) :
    comp (precompose f p) q = precompose f (comp p q) := by
  cases p with
  | old g => exact (precompose_precompose f g q).symm
  | cons g e p => rfl

/-- The empty new-arrow word is the actual left identity. -/
theorem id_comp (p : Word G a b) : comp (.old (𝟙 a)) p = p := precompose_id p

/-- The empty new-arrow word is the actual right identity. -/
theorem comp_id (p : Word G a b) : comp p (.old (𝟙 b)) = p := by
  induction p with
  | old f => simp only [comp, precompose, Category.comp_id]
  | cons f g p ih => exact congrArg (Word.cons f g) ih

/-- Whole original relative-word composition is associative. -/
theorem assoc (p : Word G a b) (q : Word G b c) (r : Word G c d) :
    comp (comp p q) r = comp p (comp q r) := by
  induction p with
  | old f => exact precompose_comp f q r
  | cons f g p ih => exact congrArg (Word.cons f g) (ih q)

/-- Concatenation preserves the exact sum of the supplied new-arrow counts. -/
theorem length_comp (p : Word G a b) (q : Word G b c) :
    (comp p q).length = p.length + q.length := by
  induction p with
  | old f => simpa only [comp, length, Nat.zero_add] using length_precompose f q
  | cons f g p ih =>
      change (comp p q).length + 1 = (p.length + 1) + q.length
      rw [ih, Nat.add_right_comm]

end Word

/-- The actual relative-word category has the same original objects and literal original Hom
segments. -/
@[instance_reducible]
def category : Category.{max u v w} C where
  Hom a b := @Word C (inferInstance : Category.{v} C) G a b
  id a := Word.old (𝟙 a)
  comp p q := Word.comp p q
  id_comp := Word.id_comp
  comp_id := Word.comp_id
  assoc := Word.assoc

/-- The original category maps into the genuine relative-word category on the same
individual objects. -/
def oldFunctor : @Functor C (inferInstance : Category.{v} C) C
    (@category C (inferInstance : Category.{v} C) G) :=
  @Functor.mk C (inferInstance : Category.{v} C) C
    (@category C (inferInstance : Category.{v} C) G)
    (fun a => a) (fun {_ _} f => Word.old f) (fun _ => rfl) (fun {_ _ _} _ _ => rfl)

end CategoryTheory.RelativeWords
