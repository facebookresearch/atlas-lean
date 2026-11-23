/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.NicomachusGeneralization

open MathlibExt.NumberTheory.NicomachusGeneralizationWanted

-- `u_1` is the constant coefficient of the series, and so is `u_0`, since `0 - 1 = 0` in `ℕ`.
example : nicomachusU 0 = 1 ∧ nicomachusU 1 = 1 := by
  simp [nicomachusU, PowerSeries.coeff_zero_eq_constantCoeff_apply]

-- The closed form at `k = 2` and `k = 3` gives the coefficients `901` of `x` and `359101` of `x²`.
example : nicomachusU 2 = 901 := by
  have hs : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h : (nicomachusU 2 : ℝ) = 901 := by
    rw [nicomachusU_eq_closedForm 2 (by norm_num), show 2 * 2 - 1 = 3 by norm_num]
    linear_combination (2700 / 44 : ℝ) * hs
  exact_mod_cast h

example : nicomachusU 3 = 359101 := by
  have hs : Real.sqrt 11 ^ 2 = 11 := Real.sq_sqrt (by norm_num)
  have h : (nicomachusU 3 : ℝ) = 359101 := by
    rw [nicomachusU_eq_closedForm 3 (by norm_num), show 2 * 3 - 1 = 5 by norm_num]
    linear_combination ((40500 * Real.sqrt 11 ^ 2 + 1345500) / 44) * hs
  exact_mod_cast h

-- The hypothesis `1 ≤ k` is needed: at `k = 0` the exponent `2k - 1` is `0`, and the closed form
-- is `-23/22`, not `u_0 = 1`.
example :
    (nicomachusU 0 : ℝ) ≠
      (5 * (10 - 3 * Real.sqrt 11) ^ (2 * 0 - 1) +
        5 * (10 + 3 * Real.sqrt 11) ^ (2 * 0 - 1) - 56) / 44 := by
  have h0 : nicomachusU 0 = 1 := by
    simp [nicomachusU, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [h0]
  norm_num

-- Starting from `u_1 = 1`, the recurrence gives `u_2 = 901`, as `(3 + 2)(23 + 22) = 15²`, and then
-- `u_3 = 359101`, as `(3 + 2 · 901)(23 + 22 · 901) = 5985²`: the coefficients of `x` and `x²`.
example : nicomachusU 2 = 901 ∧ nicomachusU 3 = 359101 := by
  have h1 : nicomachusU 1 = 1 := by
    simp [nicomachusU, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h2 : (nicomachusU 2 : ℝ) = 901 := by
    have h := nicomachusU_succ_eq 1 le_rfl
    rw [h1, show ((3 : ℝ) + 2 * ((1 : ℚ) : ℝ)) * (23 + 22 * ((1 : ℚ) : ℝ)) = 15 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at h
    exact h.trans (by norm_num)
  have h3 : (nicomachusU 3 : ℝ) = 359101 := by
    have h := nicomachusU_succ_eq 2 (by norm_num)
    rw [h2, show ((3 : ℝ) + 2 * 901) * (23 + 22 * 901) = 5985 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at h
    exact h.trans (by norm_num)
  exact ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩

-- The hypothesis `1 ≤ k` is needed: since `u_0 = u_1 = 1`, the right-hand side of the recurrence
-- at `k = 0` is `252 + 199 + 30 · 15 = 901`, not `u_1 = 1`.
example :
    (nicomachusU (0 + 1) : ℝ) ≠
      252 + 199 * (nicomachusU 0 : ℝ) +
        30 * Real.sqrt ((3 + 2 * (nicomachusU 0 : ℝ)) * (23 + 22 * (nicomachusU 0 : ℝ))) := by
  have h0 : nicomachusU 0 = 1 := by
    simp [nicomachusU, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have h1 : nicomachusU (0 + 1) = 1 := by
    simp [nicomachusU, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  rw [h0, h1, show ((3 : ℝ) + 2 * ((1 : ℚ) : ℝ)) * (23 + 22 * ((1 : ℚ) : ℝ)) = 15 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  norm_num
