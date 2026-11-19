/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.PortfolioReturn
import Mathlib.Tactic

/-!
# Tests for the one-period portfolio return

Holdings `(2, 3)` with prices `(10, 20) → (11, 22)` give initial wealth `80`,
terminal wealth `88`, portfolio return `1/10`, weights `(1/4, 3/4)` summing to
`1`, and the weighted-average instance.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.PortfolioReturn

open _root_.MathlibExt.Economics.Finance.PortfolioReturn

theorem test_portfolioReturn_eq_one_tenth :
    portfolioReturn (fun i : ℕ => if i = 0 then (2 : ℝ) else 3)
      (fun i : ℕ => if i = 0 then (10 : ℝ) else 20)
      (fun i : ℕ => if i = 0 then (11 : ℝ) else 22)
      (Finset.range 2) = 1 / 10 := by
  unfold portfolioReturn
  simp [Finset.sum_range_succ]
  norm_num

theorem test_weights_sum_to_one :
    ∑ i ∈ Finset.range 2, portfolioWeight
      ((fun i : ℕ => if i = 0 then (2 : ℝ) else 3) i)
      ((fun i : ℕ => if i = 0 then (10 : ℝ) else 20) i)
      (∑ j ∈ Finset.range 2, (fun i : ℕ => if i = 0 then (2 : ℝ) else 3) j *
        (fun i : ℕ => if i = 0 then (10 : ℝ) else 20) j) = 1 := by
  refine sum_portfolioWeight_eq_one ?_
  simp [Finset.sum_range_succ]
  norm_num

theorem test_portfolioReturn_eq_weighted_instance :
    portfolioReturn (fun i : ℕ => if i = 0 then (2 : ℝ) else 3)
      (fun i : ℕ => if i = 0 then (10 : ℝ) else 20)
      (fun i : ℕ => if i = 0 then (11 : ℝ) else 22)
      (Finset.range 2)
      = ∑ i ∈ Finset.range 2, portfolioWeight
        ((fun i : ℕ => if i = 0 then (2 : ℝ) else 3) i)
        ((fun i : ℕ => if i = 0 then (10 : ℝ) else 20) i)
        (∑ j ∈ Finset.range 2, (fun i : ℕ => if i = 0 then (2 : ℝ) else 3) j *
          (fun i : ℕ => if i = 0 then (10 : ℝ) else 20) j) *
        assetReturn ((fun i : ℕ => if i = 0 then (10 : ℝ) else 20) i)
          ((fun i : ℕ => if i = 0 then (11 : ℝ) else 22) i) := by
  refine portfolioReturn_eq_weighted ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    interval_cases i <;> simp
  · simp [Finset.sum_range_succ]
    norm_num

end MathlibExtTest.Economics.Finance.PortfolioReturn
