/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecificLimits.DiscountedGeometricSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.NormNum

/-!
# Tests for discounted geometric sums

Tests cover a negative ratio (`q = -1/2`, `c = 3`, value `2`) in `HasSum`, closed-form, and
partial-sum forms, a positive ratio (`q = 1/2`, `c = 3`, value `6`), the zero ratio
(`q = 0`, `c = 5`, value `5`), a direct three-term partial sum (`9/4`), the canonical
`discountedValue` form, and the sharpness of `|q| < 1` at `q = -1` (not summable, junk
value `0`).
-/

@[expose] public section

namespace MathlibExtTest.Analysis.SpecificLimits.DiscountedGeometricSum

open MathlibExt.DiscountedSum

/-- Negative ratio `q = -1/2`, `c = 3`: the discounted cash flows sum to `2`. -/
theorem hasSum_neg_half : HasSum (fun t : ℕ => (-1/2 : ℝ) ^ t * 3) 2 := by
  have h2 : (3 : ℝ) / (1 - (-1/2)) = 2 := by norm_num
  have h := hasSum_discountedGeometricSum (q := (-1/2 : ℝ)) (by norm_num) 3
  rw [h2] at h
  exact h

/-- Negative ratio `q = -1/2`, `c = 3`: closed form equals `2`. -/
theorem eq_neg_half : discountedGeometricSum (-1/2 : ℝ) 3 = 2 := by
  have h2 : (3 : ℝ) / (1 - (-1/2)) = 2 := by norm_num
  have h := discountedGeometricSum_eq (q := (-1/2 : ℝ)) (by norm_num) 3
  rw [h2] at h
  exact h

/-- Negative ratio `q = -1/2`, `c = 3`: partial sums converge to `2`. -/
theorem tendsto_neg_half :
    Filter.Tendsto (fun n : ℕ => ∑ t ∈ Finset.range n, (-1/2 : ℝ) ^ t * 3)
      Filter.atTop (nhds 2) := by
  have h2 : (3 : ℝ) / (1 - (-1/2)) = 2 := by norm_num
  have h := tendsto_sum_range_discountedGeometricSum (q := (-1/2 : ℝ)) (by norm_num) 3
  rw [h2] at h
  exact h

/-- Positive ratio `q = 1/2`, `c = 3`: closed form equals `6`. -/
theorem eq_half : discountedGeometricSum (1/2 : ℝ) 3 = 6 := by
  have h2 : (3 : ℝ) / (1 - 1/2) = 6 := by norm_num
  have h := discountedGeometricSum_eq (q := (1/2 : ℝ)) (by norm_num) 3
  rw [h2] at h
  exact h

/-- Zero ratio `q = 0`, `c = 5`: only date `0` counts, value `5`. -/
theorem eq_zero : discountedGeometricSum (0 : ℝ) 5 = 5 := by
  have h2 : (5 : ℝ) / (1 - 0) = 5 := by norm_num
  have h := discountedGeometricSum_eq (q := (0 : ℝ)) (by norm_num) 5
  rw [h2] at h
  exact h

/-- Direct three-term partial sum at `q = -1/2`, `c = 3`, without the pinned theorems. -/
theorem partial_sum_three :
    ∑ t ∈ Finset.range 3, (-1/2 : ℝ) ^ t * 3 = 9/4 := by
  norm_num [Finset.sum_range_succ]

/-- Canonical `discountedValue` form at `q = -1/2`, `c = 3`: value `2`. -/
theorem value_neg_half : discountedValue (-1/2 : ℝ) (fun _ => 3) = 2 := by
  have h2 : (3 : ℝ) / (1 - (-1/2)) = 2 := by norm_num
  have h := discountedGeometricSum_eq (q := (-1/2 : ℝ)) (by norm_num) 3
  rw [h2] at h
  exact h

/-- Sharpness: at `q = -1`, `c = 3` the discounted cash flows are not summable. -/
theorem not_summable_neg_one : ¬ Summable (fun t : ℕ => (-1 : ℝ) ^ t * 3) := by
  intro h
  rw [summable_mul_right_iff (show (3 : ℝ) ≠ 0 by norm_num)] at h
  rw [summable_geometric_iff_norm_lt_one] at h
  rw [Real.norm_eq_abs] at h
  norm_num at h

/-- Sharpness: at `q = -1`, `c = 3` the sum is the junk value `0`. -/
theorem eq_neg_one_junk : discountedGeometricSum (-1 : ℝ) 3 = 0 := by
  unfold discountedGeometricSum discountedValue
  exact tsum_eq_zero_of_not_summable not_summable_neg_one

end MathlibExtTest.Analysis.SpecificLimits.DiscountedGeometricSum
