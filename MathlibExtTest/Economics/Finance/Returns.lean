/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.Returns
import Mathlib.Tactic

/-!
# Tests for returns

Prices `100 → 110 → 121` give the two-period gross compounding and log
additivity instances; per-period gross returns `2, 3` give the multi-period
log sum; the price path `100 * (11/10)^n` gives the telescoping instance.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.Returns

open _root_.MathlibExt.Economics.Finance.Returns

theorem test_grossReturn_mul :
    grossReturn 100 121 = grossReturn 100 110 * grossReturn 110 121 :=
  grossReturn_mul (by norm_num) (by norm_num)

theorem test_logReturn_add :
    logReturn 100 121 = logReturn 100 110 + logReturn 110 121 :=
  logReturn_add (by norm_num) (by norm_num) (by norm_num)

theorem test_totalLogReturn :
    totalLogReturn (fun i : ℕ => if i = 0 then (2 : ℝ) else 3) (Finset.range 2) =
      Real.log 2 + Real.log 3 := by
  have hG : ∀ i ∈ Finset.range 2, 0 < (if i = 0 then (2 : ℝ) else 3) := by
    intro i _
    by_cases hi : i = 0 <;> simp [hi]
  rw [totalLogReturn_eq_sum hG]
  simp [Finset.sum_range_succ]

theorem test_grossReturn_prod_range :
    ∏ i ∈ Finset.range 2, grossReturn ((fun n : ℕ => 100 * (11 / 10 : ℝ) ^ n) i)
        ((fun n : ℕ => 100 * (11 / 10 : ℝ) ^ n) (i + 1)) =
      grossReturn ((fun n : ℕ => 100 * (11 / 10 : ℝ) ^ n) 0)
        ((fun n : ℕ => 100 * (11 / 10 : ℝ) ^ n) 2) := by
  have hP : ∀ i, (fun n : ℕ => 100 * (11 / 10 : ℝ) ^ n) i ≠ 0 := by
    intro i
    simp only
    exact mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num))
  exact grossReturn_prod_range hP

end MathlibExtTest.Economics.Finance.Returns
