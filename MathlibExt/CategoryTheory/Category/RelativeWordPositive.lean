/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordCount

/-!
# Actual positive raw-word strata and their normalized-word comparison

A raw word is positive when every target letter lies outside the
attaching image, equivalently when its new-letter count equals its raw
length. Forgetting and normalization are actual inverse maps on this
stratum, preserving every original segment and endpoint. The fixed-length
comparison is pointwise; positive strata need not be closed under simplex
operators that send letters into the attaching image.
-/

noncomputable section
universe u v wA wB
open CategoryTheory

namespace CategoryTheory.RelativeGenerators
open RelativeWords

variable {C : Type u} [Category.{v} C]
  {A : C → C → Type wA} {B : C → C → Type wB}
  (i : ∀ {a b : C}, A a b → B a b) (φ : ∀ {a b : C}, A a b → (a ⟶ b))

omit [Category.{v} C] in
/-- An original target letter contributes one exactly when it is genuinely outside the
attaching image. -/
theorem cost_eq_one_iff {a b : C} (g : B a b) :
    cost (A := A) (B := B) (@i) g = 1 ↔ g ∉ Set.range (@i a b) := by
  classical
  by_cases h : g ∈ Set.range (@i a b)
  · rw [cost, ite_eq_left h]
    exact ⟨fun e => False.elim (Nat.zero_ne_one e), fun hn => False.elim (hn h)⟩
  · rw [cost, ite_eq_right h]
    exact ⟨fun _ => h, fun _ => rfl⟩

/-- The original raw generator contributes exactly its actual zero-or-one letter count. -/
theorem count_generator {a b : C} (g : B a b) :
    count (A := A) (B := B) (@i) (generator B g) = cost (A := A) (B := B) (@i) g := rfl

/-- Forgetting normalized letters retains their entire actual new-letter count. -/
theorem count_forget {a b : C} (p : Word (newGenerators (A := A) (B := B) (@i)) a b) :
    count (A := A) (B := B) (@i) (forget (A := A) (B := B) (@i) p) = p.length := by
  induction p with
  | old f => rfl
  | cons f g p ih =>
      rw [forget, substitute_cons, count_comp, count_comp, count_generator]
      change 0 + (cost (A := A) (B := B) (@i) g.val +
          count (A := A) (B := B) (@i) (forget (A := A) (B := B) (@i) p)) = p.length + 1
      have hg := (cost_eq_one_iff (A := A) (B := B) (@i) g.val).mpr g.property
      rw [hg, ih, Nat.zero_add, Nat.add_comm]

/-- Every forgotten normalized word belongs to the actual full-count raw stratum. -/
theorem forget_positive {a b : C} (p : Word (newGenerators (A := A) (B := B) (@i)) a b) :
    count (A := A) (B := B) (@i) (forget (A := A) (B := B) (@i) p) =
      (forget (A := A) (B := B) (@i) p).length :=
  (count_forget (A := A) (B := B) (@i) p).trans (length_forget (A := A) (B := B) (@i) p).symm

/-- A raw word with full actual new-letter count has its literal forgetting-normalization
roundtrip. -/
theorem forget_normalize_of_positive {a b : C} (p : Word B a b)
    (hp : count (A := A) (B := B) (@i) p = p.length) :
    forget (A := A) (B := B) (@i) (normalize (A := A) (B := B) (@i) (@φ) p) = p := by
  induction p with
  | old f => rfl
  | cons f g p ih =>
      change cost (A := A) (B := B) (@i) g + count (A := A) (B := B) (@i) p = p.length + 1 at hp
      have hc := cost_le_one (A := A) (B := B) (@i) g
      have ht := count_le_length (A := A) (B := B) (@i) p
      have hg : cost (A := A) (B := B) (@i) g = 1 := by omega
      have htail : count (A := A) (B := B) (@i) p = p.length := by omega
      have hpos : g ∉ Set.range (@i _ _) := (cost_eq_one_iff (A := A) (B := B) (@i) g).mp hg
      rw [normalize, substitute_cons, forget_comp, forget_old, forget_comp,
        reduce, dite_eq_right hpos, forget_generator]
      change Word.comp (Word.old f) (Word.comp (generator B g)
        (forget (A := A) (B := B) (@i) (normalize (A := A) (B := B) (@i) (@φ) p))) = Word.cons f g p
      rw [ih htail]
      exact (Word.assoc _ _ _).symm.trans (cons_eq_comp B f g p).symm

/-- The pointwise actual positive raw stratum is equivalent to the original normalized word
carrier. -/
def positiveEquiv (a b : C) :
    {p : Word B a b // count (A := A) (B := B) (@i) p = p.length} ≃
      Word (newGenerators (A := A) (B := B) (@i)) a b where
  toFun p := normalize (A := A) (B := B) (@i) (@φ) p.val
  invFun p := ⟨forget (A := A) (B := B) (@i) p, forget_positive (A := A) (B := B) (@i) p⟩
  left_inv p := Subtype.ext (forget_normalize_of_positive (A := A) (B :=
    B) (@i) (@φ) p.val p.property)
  right_inv p := normalize_forget (A := A) (B := B) (@i) (@φ) p

/-- Actual positive raw words of a fixed finite length correspond to the same normalized
words of that length. -/
def positiveFixedLengthEquiv (a b : C) (n : ℕ) :
    {p : Word B a b // count (A := A) (B := B) (@i) p = p.length ∧ p.length = n} ≃
      {p : Word (newGenerators (A := A) (B := B) (@i)) a b // p.length = n} where
  toFun p := ⟨normalize (A := A) (B := B) (@i) (@φ) p.val, by
    rw [length_normalize_eq_count, p.property.1, p.property.2]⟩
  invFun p := ⟨forget (A := A) (B := B) (@i) p.val,
    forget_positive (A := A) (B := B) (@i) p.val,
    (length_forget (A := A) (B := B) (@i) p.val).trans p.property⟩
  left_inv p := Subtype.ext (forget_normalize_of_positive (A := A) (B :=
    B) (@i) (@φ) p.val p.property.1)
  right_inv p := Subtype.ext (normalize_forget (A := A) (B := B) (@i) (@φ) p.val)

end CategoryTheory.RelativeGenerators
