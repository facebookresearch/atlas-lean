/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GameTheory.MechanismDesign.VirtualSurplus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # Tests for virtual surplus maximization

Two bidders split a unit that must be allocated, so negative scores do not make the zero
allocation feasible. With both scores equal every split maximizes surplus; off the tie the
bidder with the higher score gets the whole unit.
-/

open Function MathlibExt.GameTheory.MechanismDesign

namespace VirtualSurplusTest

private def splits : Set (Bool → ℝ) :=
  {x | 0 ≤ x false ∧ 0 ≤ x true ∧ x false + x true = 1}

private def winner (j : Bool) : splits :=
  ⟨Pi.single j 1, by cases j <;> simp [splits]⟩

private noncomputable def select (w : Bool → ℝ) : splits :=
  if w false ≤ w true then winner true else winner false

-- This is a maximizer against *every fractional split*, not just against the two endpoints.
private theorem select_isMax (w : Bool → ℝ) :
    IsMaxOn (dotProduct w) splits (select w) := by
  refine isMaxOn_iff.mpr fun x ⟨h₀, h₁, hsum⟩ ↦ ?_
  by_cases h : w false ≤ w true
  · simp only [select, ite_eq_left h, winner, dotProduct_single, mul_one]
    rw [dotProduct, Fintype.sum_bool]
    nlinarith only [mul_le_mul_of_nonneg_right h h₀, congrArg (w true * ·) hsum]
  · simp only [select, ite_eq_right h, winner, dotProduct_single, mul_one]
    rw [dotProduct, Fintype.sum_bool]
    nlinarith only [mul_le_mul_of_nonneg_right (le_of_not_ge h) h₁, congrArg (w false * ·) hsum]

-- Only the score of `false` is updated; `true`'s competing score is always −1.
private abbrev opponents : Bool → ℝ := fun _ ↦ -1

private theorem tie_isMax (y : splits) :
    IsMaxOn (dotProduct (update opponents false (-1))) splits y := by
  refine isMaxOn_iff.mpr fun x hx ↦ ?_
  simp only [dotProduct, Fintype.sum_bool, update_self, update_of_ne (by decide : true ≠ false),
    opponents, neg_one_mul]
  linarith only [hx.2.2, y.property.2.2]

-- From scores (−2,−1) to the tie (−1,−1): compare *any* initial optimizer with *every* final
-- split, including ones the particular score selector would never choose.
example (x y : splits) (hx : IsMaxOn (dotProduct (update opponents false (-2))) splits x) :
    (x : Bool → ℝ) false ≤ (y : Bool → ℝ) false :=
  allocation_le_of_virtualScore_lt opponents false (by norm_num : (-2 : ℝ) < -1)
    x.property y.property hx (tie_isMax y)

-- Both endpoints of the simplex really maximize at the tie. The original winner is optimal
-- both before and after the score rise: strict allocation growth would be false.
example : IsMaxOn (dotProduct (update opponents false (-2))) splits (winner true) ∧
    IsMaxOn (dotProduct (update opponents false (-1))) splits (winner true) ∧
    IsMaxOn (dotProduct (update opponents false (-1))) splits (winner false) := by
  refine ⟨?_, tie_isMax _, tie_isMax _⟩
  simpa [select, opponents, update_of_ne (by decide : true ≠ false)] using
    select_isMax (update opponents false (-2))

-- A strictly increasing virtual map need not be the identity (and need not be positive).
example : Monotone fun b : ℝ ↦ (select (update opponents false (b - 2)) : Bool → ℝ) false :=
  monotone_allocation_of_strictMono_virtualValue opponents false (fun _ _ h ↦ sub_lt_sub_right h 2)
    _ (fun _ ↦ select_isMax _)

-- The own score max(−1,b) is flat below −1. The selector loses the tie throughout that flat
-- piece but wins once the score crosses the opposing score.
example : Monotone (fun b : ℝ ↦ (select (update opponents false (max (-1) b)) : Bool → ℝ) false) ∧
    (select (update opponents false (max (-1) (-3))) : Bool → ℝ) false = 0 ∧
    (select (update opponents false (max (-1) (-2))) : Bool → ℝ) false = 0 ∧
    (select (update opponents false (max (-1) 0)) : Bool → ℝ) false = 1 := by
  refine ⟨monotone_allocation_of_monotone_virtualValue opponents false
    (fun _ _ h ↦ max_le_max_left (-1) h) select (fun _ ↦ select_isMax _), ?_⟩
  norm_num [select, opponents, winner, Pi.single_apply, update_of_ne (by decide : true ≠ false)]

-- The constant-score raw chooser is optimal at *all* reports. Monotonicity on raw reports would
-- specifically compare 1 ≤ 0 at the ordered constant profiles 0 and 1.
example : ∃ x : (Unit → ℝ) → Unit → ℝ,
    (∀ b, x b ∈ ({0, 1} : Set (Unit → ℝ)) ∧ IsMaxOn (dotProduct 0) {0, 1} (x b)) ∧
    ¬ Monotone (fun b : ℝ ↦ x (fun _ ↦ b) ()) := by
  obtain ⟨x, hmax, h₀, h₁⟩ := exists_decreasing_allocation_of_flat_virtualValue
  refine ⟨x, hmax, fun h ↦ ?_⟩
  have hle : x 0 () ≤ x 1 () := h (zero_le_one : (0 : ℝ) ≤ 1)
  rw [h₀, h₁] at hle
  exact (not_le_of_gt zero_lt_one) hle

end VirtualSurplusTest
