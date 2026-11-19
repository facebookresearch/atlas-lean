/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.IntertemporalChoice.PresentValueBudget
import Mathlib.Tactic.NormNum

/-!
# Tests for the two-period present-value budget

At `r = 1/4` with incomes `10, 5`: saving `a = 4` finances `c = (6, 10)` and both present
values are `14`; borrowing `a = -2` finances `c = (12, 5/2)`; at `r = 0` the budget is
`c₀ + c₁ = y₀ + y₁`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.IntertemporalChoice.PresentValueBudget

open MathlibExt.Economics.Finance
open MathlibExt.Economics.IntertemporalChoice

-- Test section (required): concrete examples with exact values.

-- Saving case: r = 1/4, y = (10, 5), c = (6, 10), a = 4. Both PVs equal 14.
example : presentValue (discountFactor (1/4 : ℝ)) (Finset.range 2)
    (fun t => if t = 0 then (10 : ℝ) else 5) = 14 := by
  unfold presentValue discountFactor
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

example : presentValue (discountFactor (1/4 : ℝ)) (Finset.range 2)
    (fun t => if t = 0 then (6 : ℝ) else 10) = 14 := by
  unfold presentValue discountFactor
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

example : (∃ a : ℝ, (if (0:ℕ) = 0 then (6:ℝ) else 10) + a = (if (0:ℕ) = 0 then (10:ℝ) else 5)
    ∧ (if (1:ℕ) = 0 then (6:ℝ) else 10) = (1 + (1/4 : ℝ)) * a + (if (1:ℕ) = 0 then (10:ℝ) else 5)) ↔
    presentValue (discountFactor (1/4 : ℝ)) (Finset.range 2)
      (fun t => if t = 0 then (6 : ℝ) else 10) =
    presentValue (discountFactor (1/4 : ℝ)) (Finset.range 2)
      (fun t => if t = 0 then (10 : ℝ) else 5) := by
  have h1r : (1 : ℝ) + 1/4 ≠ 0 := by norm_num
  exact exists_asset_iff_presentValue_eq (r := (1/4 : ℝ))
    (c := fun t => if t = 0 then (6 : ℝ) else 10)
    (y := fun t => if t = 0 then (10 : ℝ) else 5) h1r

example : ∃ a : ℝ, (6:ℝ) + a = 10 ∧ (10:ℝ) = (1 + (1/4 : ℝ)) * a + 5 := by
  exact ⟨4, by norm_num, by norm_num⟩

-- Borrowing case: a = -2, c 0 = 12, c 1 = 5/2, same r and y. PV budget holds.
example : presentValue (discountFactor (1/4 : ℝ)) (Finset.range 2)
    (fun t => if t = 0 then (12 : ℝ) else 5/2) = 14 := by
  unfold presentValue discountFactor
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num

example : ∃ a : ℝ, (12:ℝ) + a = 10 ∧ ((5/2 : ℝ) = (1 + (1/4 : ℝ)) * a + 5) := by
  exact ⟨-2, by norm_num, by norm_num⟩

example : (6:ℝ) + 10 / (1 + (1/4 : ℝ)) = 10 + 5 / (1 + (1/4 : ℝ)) ∧
    (12:ℝ) + (5/2) / (1 + (1/4 : ℝ)) = 10 + 5 / (1 + (1/4 : ℝ)) := by
  constructor <;> norm_num

-- r = 0 instantiation of the budget-line equivalence.
example (y₀ y₁ c₀ c₁ : ℝ) :
    c₀ + c₁ / (1 + (0:ℝ)) = y₀ + y₁ / (1 + (0:ℝ)) ↔
    c₁ = secondPeriodConsumption 0 y₀ y₁ c₀ :=
  presentValue_budget_iff (r := (0:ℝ)) (y₀ := y₀) (y₁ := y₁) (c₀ := c₀) (c₁ := c₁) (by norm_num)

end MathlibExtTest.Economics.IntertemporalChoice.PresentValueBudget
