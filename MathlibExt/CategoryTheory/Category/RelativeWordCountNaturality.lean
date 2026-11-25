/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Category.RelativeWordCount
import MathlibExt.CategoryTheory.Category.RelativeWordRelabel

/-!
# Actual attaching-image counts under original quiver maps

A commuting inclusion square sends each attaching-image letter to an
attaching-image letter. Therefore the actual zero-or-one cost cannot
increase, and neither can the whole new-letter count under actual raw
word relabelling. These are the genuine boundary-stability conditions;
no filtration or weak-equivalence outcome is an input.
-/

noncomputable section
universe u v wA wB uD vD wAD wBD
open CategoryTheory

namespace CategoryTheory.RelativeGenerators
open RelativeWords

variable {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
  {A : C → C → Type wA} {B : C → C → Type wB}
  {AD : D → D → Type wAD} {BD : D → D → Type wBD}
  (F : C ⥤ D) (i : ∀ {a b : C}, A a b → B a b) (j : ∀ {a b : D}, AD a b → BD a b)
  (aMap : ∀ {a b : C}, A a b → AD (F.obj a) (F.obj b))
  (bMap : ∀ {a b : C}, B a b → BD (F.obj a) (F.obj b))

/-- A genuine commuting attaching-inclusion square cannot increase an individual letter's
actual new cost. -/
theorem cost_map_le (hinc : ∀ {a b : C} (g : A a b), bMap (i g) = j (aMap g))
    {a b : C} (g : B a b) :
    cost (A := AD) (B := BD) (@j) (bMap g) ≤ cost (A := A) (B := B) (@i) g := by
  classical
  by_cases h : g ∈ Set.range (@i a b)
  · let t : A a b := Classical.choose h
    have ht : i t = g := Classical.choose_spec h
    have hm : bMap g ∈ Set.range (@j (F.obj a) (F.obj b)) :=
      ⟨aMap t, (hinc t).symm.trans (congrArg (fun g : B a b => bMap g) ht)⟩
    rw [cost, ite_eq_left hm, cost, ite_eq_left h]
  · have hs : cost (A := A) (B := B) (@i) g = 1 := by rw [cost, ite_eq_right h]
    rw [hs]
    exact cost_le_one (A := AD) (B := BD) (@j) (bMap g)

/-- Actual whole raw word relabelling does not increase the original attaching-image
new-letter count. -/
theorem count_relabel_le (hinc : ∀ {a b : C} (g : A a b), bMap (i g) = j (aMap g))
    {a b : C} (p : Word B a b) :
    count (A := AD) (B := BD) (@j) (relabel F (@bMap) p) ≤ count (A := A) (B := B) (@i) p := by
  induction p with
  | old f => exact Nat.le_refl 0
  | cons f g p ih =>
      rw [relabel_cons]
      change cost (A := AD) (B := BD) (@j) (bMap g) +
          count (A := AD) (B := BD) (@j) (relabel F (@bMap) p) ≤
        cost (A := A) (B := B) (@i) g + count (A := A) (B := B) (@i) p
      exact Nat.add_le_add (cost_map_le F (@i) (@j) (@aMap) (@bMap) hinc g) ih

end CategoryTheory.RelativeGenerators
