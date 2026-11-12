/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.TwoGood
import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Strict quasiconcavity gives a unique demanded bundle (Atlas EC02.T04)

Source: J. Levin, *Consumer Theory*, Stanford Econ 202 lecture notes (2004), §2,
Proposition 5 (Convexity/Uniqueness: if preferences are strictly convex, the consumer optimum is
unique; the proof uses that `B(p, w)` is convex). Levin–Milgrom, *Introduction to Choice
Theory*, Definition 9 (convexity on a convex choice set) and Proposition 5(3) (a represented
preference is strictly convex iff its utility is strictly quasi-concave), which gives the
hypothesis used here. Mathlib has `QuasiconcaveOn` but no strict version, so
`StrictQuasiconcaveOn` is defined below. Uniqueness is "at most one": existence is EC02.T01.
-/

namespace MathlibExt.Economics.Consumer

open Matrix

/-- Strict quasiconcavity on `s`: for distinct `x, y ∈ s` and weights `a, b > 0` with `a + b = 1`,
`f (a • x + b • y) > min (f x) (f y)`. This is the strict version of Mathlib's `QuasiconcaveOn`
and the utility counterpart of strictly convex preferences. -/
def StrictQuasiconcaveOn {E : Type*} [AddCommMonoid E] [SMul ℝ E] (s : Set E) (f : E → ℝ) :
    Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → ∀ ⦃a b : ℝ⦄, 0 < a → 0 < b → a + b = 1 →
    min (f x) (f y) < f (a • x + b • y)

/-- A strictly concave function is strictly quasiconcave. -/
theorem strictQuasiconcaveOn_of_strictConcaveOn {E : Type*} [AddCommMonoid E] [SMul ℝ E]
    {s : Set E} {f : E → ℝ} (hf : StrictConcaveOn ℝ s f) : StrictQuasiconcaveOn s f := by
  intro x hx y hy hxy a b ha hb hab
  obtain ⟨hs, hconc⟩ := hf
  have hlt : a • f x + b • f y < f (a • x + b • y) := hconc hx hy hxy ha hb hab
  have ha' : 0 ≤ a := ha.le
  have hb' : 0 ≤ b := hb.le
  have hm1 : min (f x) (f y) ≤ f x := min_le_left _ _
  have hm2 : min (f x) (f y) ≤ f y := min_le_right _ _
  have h1 : a * min (f x) (f y) + b * min (f x) (f y) ≤ a * f x + b * f y :=
    add_le_add (mul_le_mul_of_nonneg_left hm1 ha') (mul_le_mul_of_nonneg_left hm2 hb')
  have h2 : min (f x) (f y) = a * min (f x) (f y) + b * min (f x) (f y) := by
    calc min (f x) (f y) = 1 * min (f x) (f y) := (one_mul _).symm
      _ = (a + b) * min (f x) (f y) := by rw [hab]
      _ = a * min (f x) (f y) + b * min (f x) (f y) := add_mul _ _ _
  have hle : min (f x) (f y) ≤ a • f x + b • f y := by
    rw [smul_eq_mul, smul_eq_mul, h2]
    exact h1
  exact lt_of_le_of_lt hle hlt

/-- The budget set of a convex consumption set is convex (used in Levin, Proposition 5). -/
theorem convex_budgetSet {L : Type*} [Fintype L] {X : Set (L → ℝ)} (hX : Convex ℝ X)
    (p : L → ℝ) (w : ℝ) : Convex ℝ (budgetSet X p w) := by
  intro x hx y hy a b ha hb hab
  simp only [budgetSet, Set.mem_ofPred_eq] at hx hy ⊢
  obtain ⟨hxX, hxp⟩ := hx
  obtain ⟨hyX, hyp⟩ := hy
  constructor
  · exact hX hxX hyX ha hb hab
  · rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    calc a * (p ⬝ᵥ x) + b * (p ⬝ᵥ y)
        ≤ a * w + b * w :=
          add_le_add (mul_le_mul_of_nonneg_left hxp ha)
            (mul_le_mul_of_nonneg_left hyp hb)
      _ = (a + b) * w := by ring
      _ = 1 * w := by rw [hab]
      _ = w := one_mul w

/-- Levin, Proposition 5: on a convex consumption set, a utility strictly quasiconcave on the
budget set has at most one Marshallian demand. -/
theorem eq_of_isMarshallianDemand {L : Type*} [Fintype L] {u : (L → ℝ) → ℝ}
    {X : Set (L → ℝ)} {p : L → ℝ} {w : ℝ} {x y : L → ℝ} (hX : Convex ℝ X)
    (hu : StrictQuasiconcaveOn (budgetSet X p w) u) (hx : IsMarshallianDemand u X p w x)
    (hy : IsMarshallianDemand u X p w y) : x = y := by
  by_contra hxy
  obtain ⟨hxmem, hxopt⟩ := hx
  obtain ⟨hymem, hyopt⟩ := hy
  have hxy_le : u x ≤ u y := hyopt x hxmem
  have hyx_le : u y ≤ u x := hxopt y hymem
  have heq : u x = u y := le_antisymm hxy_le hyx_le
  have hconv := convex_budgetSet hX p w
  have hmid : (1/2 : ℝ) • x + (1/2 : ℝ) • y ∈ budgetSet X p w :=
    hconv hxmem hymem (by norm_num) (by norm_num) (by norm_num)
  have hlt := hu hxmem hymem hxy (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (1/2:ℝ) + (1/2) = 1)
  have hmin : min (u x) (u y) = u x := by simp [heq]
  rw [hmin] at hlt
  have hopt := hxopt _ hmid
  linarith

end MathlibExt.Economics.Consumer
