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
# Actual naturality of attaching-domain reduction

An original functor and actual maps of the two generating quivers whose
inclusion and attaching squares commute induce whole-word substitution.
A source new letter may become an attaching-domain image at the target.
The actual reduction still commutes with substitution, and every supplied
letter image has length zero or one.
-/

noncomputable section
universe u v wA wB uD vD wAD wBD
open CategoryTheory

namespace CategoryTheory.RelativeGenerators
open RelativeWords

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {A : C → C → Type wA} {B : C → C → Type wB}
  {AD : D → D → Type wAD} {BD : D → D → Type wBD}
  (F : C ⥤ D)
  (i : ∀ {a b : C}, A a b → B a b) (φ : ∀ {a b : C}, A a b → (a ⟶ b))
  (j : ∀ {a b : D}, AD a b → BD a b) (ψ : ∀ {a b : D}, AD a b → (a ⟶ b))
  (aMap : ∀ {a b : C}, A a b → AD (F.obj a) (F.obj b))
  (bMap : ∀ {a b : C}, B a b → BD (F.obj a) (F.obj b))

/-- The actual image of a source new letter, allowing its target to lie in the attaching image. -/
def imageWord {a b : C} (g : newGenerators (A := A) (B := B) (@i) a b) :
    Word (newGenerators (A := AD) (B := BD) (@j)) (F.obj a) (F.obj b) :=
  reduce (A := AD) (B := BD) (@j) (@ψ) (bMap g.val)

/-- Each actual new-letter image has length at most one, even when it becomes an original arrow. -/
theorem length_imageWord_le {a b : C} (g : newGenerators (A := A) (B := B) (@i) a b) :
    (imageWord F (@i) (@j) (@ψ) (@bMap) g).length ≤ 1 :=
  length_reduce_le (A := AD) (B := BD) (@j) (@ψ) (bMap g.val)

/-- Reduction commutes with the actual original functor and both commuting generating-map
squares. -/
theorem reduce_naturality
    (hj : ∀ a b, Function.Injective (@j a b))
    (hinc : ∀ {a b : C} (g : A a b), bMap (i g) = j (aMap g))
    (hatt : ∀ {a b : C} (g : A a b), F.map (φ g) = ψ (aMap g))
    {a b : C} (g : B a b) :
    substitute F (imageWord F (@i) (@j) (@ψ) (@bMap))
      (reduce (A := A) (B := B) (@i) (@φ) g) =
      reduce (A := AD) (B := BD) (@j) (@ψ) (bMap g) := by
  classical
  by_cases h : g ∈ Set.range (@i a b)
  · let t : A a b := Classical.choose h
    have ht : i t = g := Classical.choose_spec h
    have hb : bMap g = j (aMap t) :=
      (congrArg (fun x : B a b => bMap x) ht).symm.trans (hinc t)
    calc
      _ = Word.old (F.map (φ t)) := by
        rw [reduce, dite_eq_left h, substitute_old]
      _ = Word.old (ψ (aMap t)) := congrArg (fun f => Word.old f) (hatt t)
      _ = reduce (A := AD) (B := BD) (@j) (@ψ) (j (aMap t)) :=
        (reduce_image (A := AD) (B := BD) (@j) (@ψ) hj (aMap t)).symm
      _ = _ := congrArg (fun b => reduce (A := AD) (B := BD) (@j) (@ψ) b) hb.symm
  · rw [reduce, dite_eq_right h, substitute_generator]
    rfl

end CategoryTheory.RelativeGenerators
