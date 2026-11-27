/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordsEvaluation

/-!
# Original isomorphisms and genuine new noninvertible relative words

The original category embeds without creating inverses of its arrows.
An inverse of a length-zero original word must itself have length zero,
so both inverse equations are equations of the actual original arrows.
A supplied new generator, including a loop, has length one and admits
no inverse in the actual relative-word category.
-/

noncomputable section
universe u v w
open CategoryTheory

namespace CategoryTheory.RelativeWords

variable {C : Type u} [Category.{v} C] {G : C → C → Type w}

/-- A length-zero relative word is exactly one actual original Hom arrow. -/
theorem length_eq_zero_iff {a b : C} (p : Word G a b) :
    p.length = 0 ↔ ∃ f : a ⟶ b, p = Word.old f := by
  cases p with
  | old f => exact ⟨fun _ => ⟨f, rfl⟩, fun _ => rfl⟩
  | cons f g p =>
      constructor
      · intro h
        exact False.elim (Nat.succ_ne_zero p.length h)
      · rintro ⟨f, h⟩
        cases h

/-- The actual original arrow is invertible in the relative-word category precisely when it
was already invertible. -/
theorem old_isIso_iff {a b : C} (f : a ⟶ b) :
    @IsIso C (@category C (inferInstance : Category.{v} C) G) a b (Word.old f) ↔ IsIso f := by
  constructor
  · intro h
    obtain ⟨p, hl, hr⟩ := @IsIso.out C (@category C (inferInstance : Category.{v} C) G)
      a b (Word.old f) h
    change Word.comp (Word.old f) p = Word.old (𝟙 a) at hl
    have hlen := congrArg (fun q : Word G a a => q.length) hl
    rw [Word.length_comp] at hlen
    have hp : p.length = 0 := by simpa only [Word.length, Nat.zero_add] using hlen
    obtain ⟨g, rfl⟩ := (length_eq_zero_iff p).mp hp
    change Word.old (f ≫ g) = Word.old (𝟙 a) at hl
    change Word.old (g ≫ f) = Word.old (𝟙 b) at hr
    exact ⟨⟨g, Word.old.inj hl, Word.old.inj hr⟩⟩
  · intro h
    obtain ⟨g, hl, hr⟩ := @IsIso.out C (inferInstance : Category.{v} C) a b f h
    apply @IsIso.mk C (@category C (inferInstance : Category.{v} C) G) a b (Word.old f)
    refine ⟨Word.old g, ?_, ?_⟩
    · exact congrArg (fun f => (Word.old f : Word G a a)) hl
    · exact congrArg (fun f => (Word.old f : Word G b b)) hr

/-- The actual supplied new generator has no inverse, including at an original loop pair. -/
theorem generator_not_isIso {a b : C} (g : G a b) :
    ¬ @IsIso C (@category C (inferInstance : Category.{v} C) G) a b (generator G g) := by
  intro h
  obtain ⟨p, hl, _⟩ := @IsIso.out C (@category C (inferInstance : Category.{v} C) G)
    a b (generator G g) h
  change Word.comp (generator G g) p = Word.old (𝟙 a) at hl
  have hlen := congrArg (fun q : Word G a a => q.length) hl
  rw [Word.length_comp, generator_length] at hlen
  exact Nat.succ_ne_zero p.length (by simpa only [Word.length, Nat.one_add] using hlen)

end CategoryTheory.RelativeWords
