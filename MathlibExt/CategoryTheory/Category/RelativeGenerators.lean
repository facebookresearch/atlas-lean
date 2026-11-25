/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordsEvaluation
import Mathlib.Data.Set.Function

/-!
# Actual new generators of a relative category extension

For a componentwise injective attaching map, the new generators are the
actual target arrows outside its image. An attaching-domain arrow is
evaluated by the supplied original Hom map; every remaining arrow is its
literal new length-one generator. Original objects and all loop pairs
are retained, with independent object, Hom and generating-set universes.
-/

noncomputable section
universe u v wA wB
open CategoryTheory

namespace CategoryTheory.RelativeGenerators
open RelativeWords

variable {C : Type u} [Category.{v} C]
  {A : C → C → Type wA} {B : C → C → Type wB}
  (i : ∀ {a b : C}, A a b → B a b) (f : ∀ {a b : C}, A a b → (a ⟶ b))

/-- The actual target generators outside the original attaching-domain image at the same labels. -/
abbrev newGenerators (a b : C) : Type wB := {g : B a b // g ∉ Set.range (@i a b)}

/-- Evaluate attaching-domain letters as original Hom arrows and retain all other letters
individually. -/
def reduce {a b : C} (g : B a b) : Word (newGenerators (A := A) (B := B) (@i)) a b := by
  classical
  exact if h : g ∈ Set.range (@i a b) then Word.old (f (Classical.choose h))
    else generator (newGenerators (A := A) (B := B) (@i)) ⟨g, h⟩

/-- Every attaching-domain image reduces to its same supplied original arrow. -/
theorem reduce_image (hi : ∀ a b, Function.Injective (@i a b)) {a b : C} (g : A a b) :
    reduce (A := A) (B := B) (@i) (@f) (i g) = Word.old (f g) := by
  have h : i g ∈ Set.range (@i a b) := ⟨g, rfl⟩
  rw [reduce, dite_eq_left h]
  have hc : Classical.choose h = g := hi a b (Classical.choose_spec h)
  exact congrArg (fun a => Word.old (f a)) hc

/-- Every actual new target letter remains its same individually supplied length-one generator. -/
theorem reduce_new {a b : C} (g : newGenerators (A := A) (B := B) (@i) a b) :
    reduce (A := A) (B := B) (@i) (@f) g.val = generator (newGenerators (A := A) (B :=
      B) (@i)) g := by
  rw [reduce, dite_eq_right g.property]

/-- Attaching-domain evaluation cannot increase a supplied letter beyond length one. -/
theorem length_reduce_le {a b : C} (g : B a b) : (reduce (A := A) (B :=
  B) (@i) (@f) g).length ≤ 1 := by
  classical
  by_cases h : g ∈ Set.range (@i a b)
  · rw [reduce, dite_eq_left h]
    exact Nat.zero_le 1
  · rw [reduce, dite_eq_right h]
    exact Nat.le_refl 1

end CategoryTheory.RelativeGenerators
