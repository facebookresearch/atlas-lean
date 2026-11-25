/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DivisorsShortIntervalExistsShortIntervalDivisorCountLeOfWindowThetaSq
import Mathlib.Tactic.NormNum

/-! # Tests for divisors in windows of length `n ^ (θ ^ 2 - ε)` -/

namespace MathlibExtTest.NumberTheory.DivisorsShortIntervalExistsShortIntervalDivisorCountLeOfWindowThetaSq

open MetaMathlibExt

-- At θ = 1/2 and ε = 1/8 the window bound applies to every n ≥ 1.
example : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    (shortIntervalDivisorCount n ((n : ℝ) ^ (1 / 2 : ℝ))
        ((n : ℝ) ^ ((1 / 2 : ℝ) ^ 2 - 1 / 8)) : ℝ) ≤
      C * ((1 / 2 : ℝ) * (1 - 1 / 2) / (1 / 8 : ℝ) + 1 / ((1 / 2 : ℝ) * (1 - 1 / 2))) := by
  obtain ⟨C, hC⟩ := exists_shortIntervalDivisorCount_le_of_window_theta_sq
  exact ⟨C, fun n hn => hC n hn (1 / 2) (1 / 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)⟩

-- With θ = 1/2 and ε = 1/8 the window is `[√n, √n + n ^ (1/8)]` and the bound is `6 * C`.
example : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    (shortIntervalDivisorCount n ((n : ℝ) ^ (1 / 2 : ℝ)) ((n : ℝ) ^ (1 / 8 : ℝ)) : ℝ)
      ≤ C * 6 := by
  obtain ⟨C, hC⟩ := exists_shortIntervalDivisorCount_le_of_window_theta_sq
  refine ⟨C, fun n hn => ?_⟩
  have h := hC n hn (1 / 2) (1 / 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hexp : (1 / 2 : ℝ) ^ 2 - 1 / 8 = 1 / 8 := by norm_num
  have hval : (1 / 2 : ℝ) * (1 - 1 / 2) / (1 / 8 : ℝ)
      + 1 / ((1 / 2 : ℝ) * (1 - 1 / 2)) = 6 := by norm_num
  rw [hexp, hval] at h
  exact h

end MathlibExtTest.NumberTheory.DivisorsShortIntervalExistsShortIntervalDivisorCountLeOfWindowThetaSq
