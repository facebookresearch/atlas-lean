/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.Trigonometric.CosineAlternatingIntegralLimit

/-! # Tests for the alternating cosine integral limit -/

namespace MathlibExtTest.CosineAlternatingIntegralLimit

open Real Filter Topology MetaMathlibExt

private noncomputable def alternatingIntegral (q m : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 m,
    ((∫ x in (((l : ℝ) - 1) * π / ((2 * m : ℝ) - 1))..((l : ℝ) * π / ((2 * m : ℝ) + 1)),
        (cos (q * x) - cos (q * (2 * m : ℝ) * x))) -
      ∫ x in ((l : ℝ) * π / ((2 * m : ℝ) + 1))..((l : ℝ) * π / ((2 * m : ℝ) - 1)),
        (cos (q * x) - cos (q * (2 * m : ℝ) * x)))

-- The statement includes the degenerate multiplier, with no division by it needed.
example : Tendsto (alternatingIntegral 0) atTop (𝓝 0) := by
  have h := tendsto_sum_integral_cos_sub_cos_even_even (q := 0) (by decide)
  rw [ite_eq_left (show (0 : ℕ) % 4 = 0 by decide)] at h
  exact h

-- A positive multiple of four takes the zero branch.
example : Tendsto (alternatingIntegral 4) atTop (𝓝 0) := by
  have h := tendsto_sum_integral_cos_sub_cos_even_even (q := 4) (by decide)
  rw [ite_eq_left (show (4 : ℕ) % 4 = 0 by decide)] at h
  exact h

-- In the other even residue class, the nonzero limit keeps the factor `16 / q ^ 2`.
example : Tendsto (alternatingIntegral 2) atTop (𝓝 (4 / π)) := by
  have h := tendsto_sum_integral_cos_sub_cos_even_even (q := 2) (by decide)
  have hlim : 16 / (((2 : ℕ) : ℝ) ^ 2 * π) = 4 / π := by push_cast; ring
  rw [ite_eq_right (show (2 : ℕ) % 4 ≠ 0 by decide), hlim] at h
  exact h

/-- info: 'MetaMathlibExt.tendsto_sum_integral_cos_sub_cos_even_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms MetaMathlibExt.tendsto_sum_integral_cos_sub_cos_even_even

end MathlibExtTest.CosineAlternatingIntegralLimit
