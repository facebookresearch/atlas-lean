/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Numerical.RatIntervalOps
public meta import MathlibExt.Analysis.Numerical.RatIntervalOps

namespace MathlibExt.Analysis.Numerical.Certified.RatInterval

/- Tests for interval multiplication and division: computed enclosures are
verified with `Encloses.mul` / `Encloses.div` (Moore, R. E.,
*Interval Analysis*, Prentice-Hall, 1966, Ch. 2). -/

/-- Multiplication of mixed-sign intervals computes the min/max corner products. -/
theorem test_mul_mixed_endpoints :
    ((⟨-1, 2⟩ : RatInterval).mul ⟨-3, 4⟩).lower = -6 ∧
      ((⟨-1, 2⟩ : RatInterval).mul ⟨-3, 4⟩).upper = 8 := by
  constructor
  · rw [mul_lower]
    norm_num
  · rw [mul_upper]
    norm_num

/-- `Encloses.mul` verifies a computed mixed-sign product enclosure. -/
theorem test_mul_mixed_encloses :
    ((⟨-1, 2⟩ : RatInterval).mul ⟨-3, 4⟩).Encloses ((-1/2 : ℝ) * 3) := by
  apply Encloses.mul
  · show ((-1 : ℚ) : ℝ) ≤ (-1/2 : ℝ) ∧ (-1/2 : ℝ) ≤ ((2 : ℚ) : ℝ)
    norm_num
  · show ((-3 : ℚ) : ℝ) ≤ (3 : ℝ) ∧ (3 : ℝ) ≤ ((4 : ℚ) : ℝ)
    norm_num

/-- Nonnegative intervals multiply corner-to-corner. -/
theorem test_mul_nonneg_char :
    ((⟨1, 2⟩ : RatInterval).mul ⟨3, 4⟩) = ⟨1 * 3, 2 * 4⟩ :=
  mul_of_nonneg (by show (0:ℚ) ≤ 1; norm_num) (by show (1:ℚ) ≤ 2; norm_num)
    (by show (0:ℚ) ≤ 3; norm_num) (by show (3:ℚ) ≤ 4; norm_num)

/-- Division by a positive interval. -/
theorem test_div_pos_encloses :
    ((⟨1, 2⟩ : RatInterval).div ⟨1, 4⟩).Encloses ((3/2 : ℝ) / 2) := by
  refine Encloses.div (Or.inr ?h0) ?hx ?hy
  · show (0:ℚ) < 1
    norm_num
  · show ((1:ℚ):ℝ) ≤ (3/2:ℝ) ∧ (3/2:ℝ) ≤ ((2:ℚ):ℝ)
    norm_num
  · show ((1:ℚ):ℝ) ≤ (2:ℝ) ∧ (2:ℝ) ≤ ((4:ℚ):ℝ)
    norm_num

/-- Division by a negative interval. -/
theorem test_div_neg_encloses :
    ((⟨1, 2⟩ : RatInterval).div ⟨-4, -1⟩).Encloses ((3/2 : ℝ) / -2) := by
  refine Encloses.div (Or.inl ?h0) ?hx ?hy
  · show (-1:ℚ) < 0
    norm_num
  · show ((1:ℚ):ℝ) ≤ (3/2:ℝ) ∧ (3/2:ℝ) ≤ ((2:ℚ):ℝ)
    norm_num
  · show ((-4:ℚ):ℝ) ≤ (-2:ℝ) ∧ (-2:ℝ) ≤ ((-1:ℚ):ℝ)
    norm_num

#print axioms Encloses.mul
#print axioms Encloses.inv
#print axioms Encloses.div
#print axioms mul_of_nonneg
#print axioms test_mul_mixed_endpoints
#print axioms test_mul_mixed_encloses
#print axioms test_mul_nonneg_char
#print axioms test_div_pos_encloses
#print axioms test_div_neg_encloses

end MathlibExt.Analysis.Numerical.Certified.RatInterval
