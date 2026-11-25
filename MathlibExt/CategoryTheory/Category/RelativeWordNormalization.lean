/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeGenerators
import MathlibExt.CategoryTheory.Category.RelativeWordsSubstitution

/-!
# Actual normalization and forgetting of whole relative words

Raw target letters normalize by the actual attaching-domain evaluation.
Normalized letters forget to their same original target values. The
whole normalization-forgetting roundtrip is literal on every original
word and endpoint. Forgetting keeps the exact word length; normalization
cannot increase it, including original identity and loop segments.
-/

noncomputable section
universe u v wA wB
open CategoryTheory

namespace CategoryTheory.RelativeGenerators
open RelativeWords

variable {C : Type u} [Category.{v} C]
  {A : C → C → Type wA} {B : C → C → Type wB}
  (i : ∀ {a b : C}, A a b → B a b) (φ : ∀ {a b : C}, A a b → (a ⟶ b))

/-- Normalize the whole raw original word by the actual attaching-domain reduction. -/
def normalize {a b : C} (p : Word B a b) : Word (newGenerators (A := A) (B := B) (@i)) a b :=
  substitute (𝟭 C) (fun g => reduce (A := A) (B := B) (@i) (@φ) g) p

/-- Forget normalized letter subtypes, retaining their same actual original target arrows. -/
def forget {a b : C} (p : Word (newGenerators (A := A) (B := B) (@i)) a b) : Word B a b :=
  substitute (𝟭 C) (fun g => generator B g.val) p

/-- Normalization retains an original Hom segment as that same length-zero segment. -/
theorem normalize_old {a b : C} (f : a ⟶ b) :
    normalize (A := A) (B := B) (@i) (@φ) (Word.old f) = Word.old f := rfl

/-- Normalization of a supplied target generator is its actual original attaching-domain
reduction. -/
theorem normalize_generator {a b : C} (g : B a b) :
    normalize (A := A) (B := B) (@i) (@φ) (generator B g) =
      reduce (A := A) (B := B) (@i) (@φ) g :=
  substitute_generator (𝟭 C) _ g

/-- Forgetting retains an original Hom segment as the same actual segment. -/
theorem forget_old {a b : C} (f : a ⟶ b) :
    forget (A := A) (B := B) (@i) (Word.old f) = Word.old f := rfl

/-- Forgetting reads a normalized generator back as its same original target value. -/
theorem forget_generator {a b : C} (g : newGenerators (A := A) (B := B) (@i) a b) :
    forget (A := A) (B := B) (@i) (generator (newGenerators (A := A) (B := B) (@i)) g) =
      generator B g.val := substitute_generator (𝟭 C) _ g

/-- Normalization preserves whole original word composition. -/
theorem normalize_comp {a b c : C} (p : Word B a b) (q : Word B b c) :
    normalize (A := A) (B := B) (@i) (@φ) (Word.comp p q) =
      Word.comp (normalize (A := A) (B := B) (@i) (@φ) p)
        (normalize (A := A) (B := B) (@i) (@φ) q) := substitute_comp (𝟭 C) _ p q

/-- Forgetting preserves whole original word composition. -/
theorem forget_comp {a b c : C}
    (p : Word (newGenerators (A := A) (B := B) (@i)) a b)
    (q : Word (newGenerators (A := A) (B := B) (@i)) b c) :
    forget (A := A) (B := B) (@i) (Word.comp p q) =
      Word.comp (forget (A := A) (B := B) (@i) p) (forget (A := A) (B := B) (@i) q) :=
  substitute_comp (𝟭 C) _ p q

/-- Actual attaching-domain normalization does not increase any whole original word length. -/
theorem length_normalize_le {a b : C} (p : Word B a b) :
    (normalize (A := A) (B := B) (@i) (@φ) p).length ≤ p.length :=
  length_substitute_le (𝟭 C) (fun g => reduce (A := A) (B := B) (@i) (@φ) g)
    (fun g => length_reduce_le (A := A) (B := B) (@i) (@φ) g) p

/-- Forgetting retains the exact finite count of original normalized letters. -/
theorem length_forget {a b : C} (p : Word (newGenerators (A := A) (B := B) (@i)) a b) :
    (forget (A := A) (B := B) (@i) p).length = p.length := by
  induction p with
  | old f => rfl
  | cons f g p ih =>
      rw [forget, substitute_cons, Word.length_comp, Word.length_comp, generator_length]
      change 0 + (1 + (forget (A := A) (B := B) (@i) p).length) = p.length + 1
      rw [ih, Nat.zero_add, Nat.add_comm]

/-- The actual entire normalized word has a literal normalization-forgetting roundtrip. -/
theorem normalize_forget {a b : C} (p : Word (newGenerators (A := A) (B := B) (@i)) a b) :
    normalize (A := A) (B := B) (@i) (@φ) (forget (A := A) (B := B) (@i) p) = p := by
  induction p with
  | old f => rfl
  | cons f g p ih =>
      rw [forget, substitute_cons, normalize_comp, normalize_old, normalize_comp,
        normalize_generator, reduce_new]
      change Word.comp (Word.old f)
        (Word.comp (generator (newGenerators (A := A) (B := B) (@i)) g)
          (normalize (A := A) (B := B) (@i) (@φ) (forget (A := A) (B := B) (@i) p))) =
        Word.cons f g p
      rw [ih]
      exact (Word.assoc _ _ _).symm.trans (cons_eq_comp _ f g p).symm

end CategoryTheory.RelativeGenerators
