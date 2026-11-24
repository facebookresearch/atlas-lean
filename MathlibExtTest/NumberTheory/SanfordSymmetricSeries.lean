/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SanfordSymmetricSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! # A dyadic specialization of Sanford's symmetric series -/

open Real MetaMathlibExt

-- At a = 1/3 the first argument is 2/9 and the series sums to L(1/2) = π²/12.
example :
    let L (x : ℝ) := li2PowerSeries x + log x * log (1 - x) / 2
    ∑' n : ℕ, L (2 ^ (n + 1) / (2 ^ (n + 2) - 1) ^ 2) = π ^ 2 / 12 := by
  intro L
  have h := rogersDilog_sanford_symmetric_series (a := 1 / 3) (by norm_num) (by norm_num)
  have hs : ∑' n : ℕ, L ((1 / 3) ^ 2 * (1 / 3) ^ (n + 1) * (2 / 3) ^ (n + 1) /
      ((2 / 3) ^ (n + 2) - (1 / 3) ^ (n + 2)) ^ 2) = L (1 / 2) := by
    simpa only [L, li2PowerSeries, Nat.cast_add, Nat.cast_one,
      show (1 / 2 - 1 / 3 / 2 : ℝ) = 1 / 3 by norm_num,
      show (1 / 2 + 1 / 3 / 2 : ℝ) = 2 / 3 by norm_num,
      show ((1 - 1 / 3) / (1 + 1 / 3) : ℝ) = 1 / 2 by norm_num] using h
  have hhalf : 1 - (1 / 2 : ℝ) = 1 / 2 := by norm_num
  have href := li2PowerSeries_reflection (z := 1 / 2) (by constructor <;> norm_num)
  rw [hhalf] at href
  have hval : L (1 / 2) = π ^ 2 / 12 := by
    dsimp [L]
    rw [hhalf]
    linarith
  rw [← hval, ← hs]
  apply tsum_congr
  intro n
  congr 1
  simp only [div_pow, one_pow, ← sub_div]
  rw [div_div_eq_mul_div]
  congr 1
  rw [pow_succ (3 : ℝ) (n + 1)]
  field_simp
