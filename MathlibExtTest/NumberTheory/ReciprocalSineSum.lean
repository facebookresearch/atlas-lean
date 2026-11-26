/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ReciprocalSineSum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for the reciprocal sine bounds -/

namespace MathlibExtTest.ReciprocalSineSum

open Finset MetaMathlibExt

-- The smallest prime and interval allowed by the hypotheses.
example :
    1 / |Real.sin (Real.pi / 3)| <
      (3 / Real.pi) * (Real.eulerMascheroniConstant + 1 / 2) + 3 / (4 * Real.pi) := by
  have h := sum_one_div_abs_sin_lt 3 (by decide) 1 (by decide) 1 (by decide) (by norm_num)
  norm_num [Icc_self] at h ⊢
  convert h using 1
  ring

-- A negative multiplier permutes the three least absolute representatives
-- at the largest admissible length for the prime 7.
example :
    ∑ h ∈ Icc (1 : ℕ) 3, 1 / |Real.sin (Real.pi * (-2) * (h : ℝ) / 7)| <
      (7 / Real.pi) * (Real.log 3 + Real.eulerMascheroniConstant + 1 / 6) +
        21 / (10 * Real.pi) := by
  have h := sum_one_div_abs_sin_lt 7 (by decide) (-2) (by decide) 3 (by decide) (by norm_num)
  norm_num at h ⊢
  convert h using 1
  ring

-- At `p = 7`, `a = 1` and `B = 2` the hypotheses hold and the bound applies.
example : ∑ h ∈ Icc (1 : ℕ) 2, min (2 : ℝ) (1 / |Real.sin (Real.pi * 1 * h / 7)|) <
    (7 / Real.pi) * (Real.log (Real.pi * 2 ^ 2 / 7) + 1 + Real.pi * 2 / 7) +
      7 * 2 * (2 + 1) / (Real.pi * ((7 : ℝ) ^ 2 - (2 : ℝ) ^ 2)) := by
  have hp : Nat.Prime 7 := by decide
  have ha : ¬ ((7 : ℕ) : ℤ) ∣ (1 : ℤ) := by decide
  have hB₁ : Real.sqrt (((7 : ℕ) : ℝ) / Real.pi) < (((2 : ℕ) : ℝ)) := by
    norm_num only [Nat.cast_ofNat]
    rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ Real.pi_pos]
    have h2 : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [h2]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have hB₂ : (((2 : ℕ) : ℝ)) < (((7 : ℕ) : ℝ)) / 2 := by norm_num
  have h := MetaMathlibExt.sum_min_one_div_abs_sin_lt 7 hp 1 ha 2 hB₁ hB₂
  simpa using h

-- At `p = 5`, `a = 1` and `B = 2` the hypotheses hold and the bound applies.
example : ∑ h ∈ Icc (1 : ℕ) 2, min (2 : ℝ) (1 / |Real.sin (Real.pi * 1 * h / 5)|) <
    (5 / Real.pi) * (Real.log (Real.pi * 2 ^ 2 / 5) + 1 + Real.pi * 2 / 5) +
      5 * 2 * (2 + 1) / (Real.pi * ((5 : ℝ) ^ 2 - (2 : ℝ) ^ 2)) := by
  have hp : Nat.Prime 5 := by decide
  have ha : ¬ ((5 : ℕ) : ℤ) ∣ (1 : ℤ) := by decide
  have hB₁ : Real.sqrt (((5 : ℕ) : ℝ) / Real.pi) < (((2 : ℕ) : ℝ)) := by
    norm_num only [Nat.cast_ofNat]
    rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ Real.pi_pos]
    have h2 : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [h2]
    have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
    linarith
  have hB₂ : (((2 : ℕ) : ℝ)) < (((5 : ℕ) : ℝ)) / 2 := by norm_num
  have h := MetaMathlibExt.sum_min_one_div_abs_sin_lt 5 hp 1 ha 2 hB₁ hB₂
  simpa using h

end MathlibExtTest.ReciprocalSineSum
