/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeGenerators

/-!
# Actual evaluation of attaching-domain reduction

For an original functor and actual target-generator images whose
attaching square commutes, reducing an original target letter and
evaluating it reads back that same supplied target image. Both original
attaching-domain letters and genuine new loop letters are included.
-/

noncomputable section
universe u v wA wB uD vD
open CategoryTheory

namespace CategoryTheory.RelativeGenerators
open RelativeWords

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {A : C → C → Type wA} {B : C → C → Type wB}
  (F : C ⥤ D) (i : ∀ {a b : C}, A a b → B a b) (φ : ∀ {a b : C}, A a b → (a ⟶ b))
  (m : ∀ {a b : C}, B a b → (F.obj a ⟶ F.obj b))

/-- The same actual target-generator image is read back after original attaching-domain
reduction. -/
theorem eval_reduce (hm : ∀ {a b : C} (g : A a b), m (i g) = F.map (φ g))
    {a b : C} (g : B a b) :
    eval F (fun e => m e.val) (reduce (A := A) (B := B) (@i) (@φ) g) = m g := by
  classical
  by_cases h : g ∈ Set.range (@i a b)
  · rw [reduce, dite_eq_left h]
    have ht : i (Classical.choose h) = g := Classical.choose_spec h
    exact (hm (Classical.choose h)).symm.trans (congrArg (fun g : B a b => m g) ht)
  · rw [reduce, dite_eq_right h, eval_generator]

end CategoryTheory.RelativeGenerators
