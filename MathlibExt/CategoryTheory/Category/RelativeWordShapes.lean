/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWords

/-!
# Actual finite original label sequences and word factor spaces

The shape records each individually supplied source and target of the
new letters. Its factor space retains all intervening original Hom
segments and the whole target letters. Decoding gives exactly the same
relative word and exact finite length, including the original nullary
Hom stage, loops and arbitrary repeated intermediate labels.
-/

universe u v w
open CategoryTheory

namespace CategoryTheory.RelativeWords

/-- The actual finite sequence of individually supplied new-letter source and target labels. -/
inductive Shape (C : Type u) : ℕ → Type u
  | nil : Shape C 0
  | cons {n : ℕ} (x y : C) (s : Shape C n) : Shape C (n + 1)

variable {C : Type u} [Category.{v} C] (G : C → C → Type w)

/-- The actual original Hom-segment and new-letter product at a supplied finite label shape. -/
def Cells : {n : ℕ} → Shape C n → (a b : C) → Type (max u v w)
  | 0, .nil, a, b => ULift.{max u w} (@Quiver.Hom.{v, u} C (inferInstance : Quiver.{v} C) a b)
  | _n + 1, .cons x y s, a, b =>
    (@Quiver.Hom.{v, u} C (inferInstance : Quiver.{v} C) a x) × G x y × Cells s y b

/-- Decode every actual finite product of original segments and letters as its whole
original word. -/
def decode : {n : ℕ} → (s : Shape C n) → {a b : C} → Cells G s a b → Word G a b
  | 0, .nil, _, _, f => Word.old f.down
  | _n + 1, .cons _x _y s, _, _, p => Word.cons p.1 p.2.1 (decode s p.2.2)

/-- Every decoded original factor word has exactly its supplied finite new-letter length. -/
theorem length_decode {n : ℕ} (s : Shape C n) {a b : C} (p : Cells G s a b) :
    (decode G s p).length = n := by
  induction s generalizing a b with
  | nil => rfl
  | cons x y s ih => exact congrArg (fun n => n + 1) (ih p.2.2)

/-- Every whole relative word has its actual original label sequence and product factors. -/
def encode : {a b : C} → (p : Word G a b) → Σ s : Shape C p.length, Cells G s a b
  | _, _, .old f => ⟨Shape.nil, ⟨f⟩⟩
  | _, _, @Word.cons _ _ _ a x y b f g p =>
      let t := encode p
      ⟨Shape.cons x y t.1, (f, g, t.2)⟩

/-- Decoding the actual encoded label sequence and factors returns the same entire original word. -/
theorem decode_encode {a b : C} (p : Word G a b) : decode G (encode G p).1 (encode G p).2 = p := by
  induction p with
  | old f => rfl
  | cons f g p ih => exact congrArg (Word.cons f g) ih

end CategoryTheory.RelativeWords
