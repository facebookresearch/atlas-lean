/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticForms.GaussClassNumberBound
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Tests for `gaussClassNumber_neg_four_mul_lt`
-/

namespace MetaMathlibExt.GaussClassNumberBoundTest

/-- Hua's bound implies the simpler bound `h(-4D) < √D (3 + log D)`, using `π > 3` and
`log 2 < 0.7`. -/
private theorem gaussClassNumber_lt_sqrt_mul (D : ℕ) (hD : 0 < D) :
    (gaussClassNumber (-4 * D) : ℝ) < Real.sqrt D * (3 + Real.log D) := by
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr (by exact_mod_cast hD)
  have hlog : Real.log (2 * Real.exp 1 * Real.sqrt D) = Real.log 2 + 1 + Real.log D / 2 := by
    rw [Real.log_mul (by positivity) hs.ne', Real.log_mul (by norm_num) (Real.exp_pos 1).ne',
      Real.log_exp, Real.log_sqrt (Nat.cast_nonneg _)]
  have hlD : 0 ≤ Real.log D := Real.log_nonneg (by exact_mod_cast hD)
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_pos one_lt_two
  have hpi := Real.pi_gt_three
  have hL : 4 / 3 * (Real.log 2 + 1 + Real.log D / 2) ≤ 3 + Real.log D := by linarith
  calc (gaussClassNumber (-4 * D) : ℝ)
      < 4 / Real.pi * Real.sqrt D * (Real.log 2 + 1 + Real.log D / 2) :=
        hlog ▸ gaussClassNumber_neg_four_mul_lt D hD
    _ ≤ 4 / 3 * Real.sqrt D * (Real.log 2 + 1 + Real.log D / 2) := by
        gcongr
    _ = Real.sqrt D * (4 / 3 * (Real.log 2 + 1 + Real.log D / 2)) := by ring
    _ ≤ Real.sqrt D * (3 + Real.log D) := by gcongr

-- At `D = 1` the bound gives `h(-4) < 3`; the class number itself is `1`.
example : gaussClassNumber (-4) < 3 ∧ gaussClassNumber (-4) = 1 := by
  refine ⟨?_, by decide +kernel⟩
  have h := gaussClassNumber_lt_sqrt_mul 1 one_pos
  norm_num at h
  exact_mod_cast h

-- At `D = 10⁶`, far beyond a direct count, the bound gives `h(-4 · 10⁶) < 17000`.
example : gaussClassNumber (-4 * (10 ^ 6 : ℕ)) < 17000 := by
  have h := gaussClassNumber_lt_sqrt_mul (10 ^ 6) (by norm_num)
  have hsqrt : Real.sqrt ((10 ^ 6 : ℕ) : ℝ) = 1000 := by
    rw [show ((10 ^ 6 : ℕ) : ℝ) = 1000 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hlog : Real.log ((10 ^ 6 : ℕ) : ℝ) < 14 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num), show (14 : ℝ) = ((14 : ℕ) : ℝ) by norm_num,
      ← Real.exp_one_pow]
    calc ((10 ^ 6 : ℕ) : ℝ) < 2.7182818283 ^ 14 := by norm_num
      _ < Real.exp 1 ^ 14 := by gcongr; exact Real.exp_one_gt_d9
  rw [hsqrt] at h
  have : (gaussClassNumber (-4 * (10 ^ 6 : ℕ)) : ℝ) < 17000 := by linarith
  exact_mod_cast this

end MetaMathlibExt.GaussClassNumberBoundTest
