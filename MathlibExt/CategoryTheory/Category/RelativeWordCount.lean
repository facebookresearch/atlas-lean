/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordNormalization
import Lean.Elab.Tactic.Omega

/-!
# Actual new-letter counts in a whole relative word

An attaching-image letter contributes zero; every other original target
letter contributes one. The normalized word has exactly this count.
The count never exceeds the whole raw word length, and is additive under
original concatenation. These are the actual numeric boundary conditions
for the length filtration, including empty words and loop segments.
-/

noncomputable section
universe u v wA wB
open CategoryTheory

namespace CategoryTheory.RelativeGenerators
open RelativeWords

variable {C : Type u} [Category.{v} C]
  {A : C → C → Type wA} {B : C → C → Type wB}
  (i : ∀ {a b : C}, A a b → B a b) (φ : ∀ {a b : C}, A a b → (a ⟶ b))

/-- The actual zero-or-one contribution of a supplied original target letter. -/
def cost {a b : C} (g : B a b) : ℕ := by
  classical
  exact if g ∈ Set.range (@i a b) then 0 else 1

omit [Category.{v} C] in
/-- Every actual letter contributes at most one to the normalized word. -/
theorem cost_le_one {a b : C} (g : B a b) : cost (A := A) (B := B) (@i) g ≤ 1 := by
  classical
  by_cases h : g ∈ Set.range (@i a b) <;> simp only [cost, h, ite_true, ite_false] <;> omega

/-- The actual normalized contribution is exactly the original attaching-image test. -/
theorem length_reduce_eq_cost {a b : C} (g : B a b) :
    (reduce (A := A) (B := B) (@i) (@φ) g).length = cost (A := A) (B := B) (@i) g := by
  classical
  by_cases h : g ∈ Set.range (@i a b)
  · rw [reduce, dite_eq_left h, cost, ite_eq_left h]
    rfl
  · rw [reduce, dite_eq_right h, cost, ite_eq_right h]
    rfl

/-- Count all actual new target letters in the whole original raw word. -/
def count : {a b : C} → Word B a b → ℕ
  | _, _, .old _ => 0
  | _, _, @Word.cons _ _ _ a x y b _f g p =>
    cost (A := A) (B := B) (@i) (a := x) (b := y) g + count p

/-- Original precomposition retains the entire actual new-letter count. -/
theorem count_precompose {a b c : C} (f : a ⟶ b) (p : Word B b c) :
    count (A := A) (B := B) (@i) (Word.precompose f p) = count (A := A) (B := B) (@i) p := by
  cases p <;> rfl

/-- Whole original concatenation adds the actual new-letter counts. -/
theorem count_comp {a b c : C} (p : Word B a b) (q : Word B b c) :
    count (A := A) (B := B) (@i) (Word.comp p q) =
      count (A := A) (B := B) (@i) p + count (A := A) (B := B) (@i) q := by
  induction p with
  | old f =>
      simpa only [Word.comp, count, Nat.zero_add] using
        count_precompose (A := A) (B := B) (@i) f q
  | cons f g p ih =>
      change cost (A := A) (B := B) (@i) g + count (A := A) (B := B) (@i) (Word.comp p q) =
        (cost (A := A) (B := B) (@i) g + count (A := A) (B := B) (@i) p) +
          count (A := A) (B := B) (@i) q
      rw [ih, Nat.add_assoc]

/-- The actual normalized count is bounded by the original finite word length. -/
theorem count_le_length {a b : C} (p : Word B a b) : count (A := A) (B := B) (@i) p ≤ p.length := by
  induction p with
  | old f => exact Nat.le_refl 0
  | cons f g p ih =>
      change cost (A := A) (B := B) (@i) g + count (A := A) (B := B) (@i) p ≤ p.length + 1
      have hg := cost_le_one (A := A) (B := B) (@i) g
      omega

/-- The whole normalized word length is exactly its original new-letter count. -/
theorem length_normalize_eq_count {a b : C} (p : Word B a b) :
    (normalize (A := A) (B := B) (@i) (@φ) p).length = count (A := A) (B := B) (@i) p := by
  induction p with
  | old f => rfl
  | cons f g p ih =>
      rw [normalize, substitute_cons, Word.length_comp, Word.length_comp]
      change 0 + ((reduce (A := A) (B := B) (@i) (@φ) g).length +
          (normalize (A := A) (B := B) (@i) (@φ) p).length) =
        cost (A := A) (B := B) (@i) g + count (A := A) (B := B) (@i) p
      rw [length_reduce_eq_cost, ih, Nat.zero_add]

end CategoryTheory.RelativeGenerators
