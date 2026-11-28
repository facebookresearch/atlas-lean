/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import MathlibExt.NumberTheory.DivRunCountOne

namespace MetaMathlibExt

-- At bound zero the only candidate has a zero divisor.
example : divRunCount 0 1 = 0 := by decide

-- Count directly from the run predicate at a bound with more than one divisor magnitude.
example : divRunCount 2 1 = 1980 := by decide +kernel

-- The closed formula agrees with that direct count.
example : divRunCount 2 1 = 1980 := by
  rw [divRunCount_one]
  decide

-- At radius three the concrete error lies between consecutive integers, below the uniform bound.
example :
    let error := |(divRunCount 3 1 : ℝ) - 32 * 3 ^ 4 * Real.log 3|
    6028 < error ∧ error < 6029 ∧ error ≤ 238 * 3 ^ 4 := by
  dsimp only
  have hcount : divRunCount 3 1 = 8876 := by
    rw [divRunCount_one]
    decide
  simp only [hcount, Nat.cast_ofNat]
  have hlo : 6028 < (8876 : ℝ) - 32 * 3 ^ 4 * Real.log 3 := by
    linarith only [Real.log_three_lt_d9]
  have hhi : (8876 : ℝ) - 32 * 3 ^ 4 * Real.log 3 < 6029 := by
    linarith only [Real.log_three_gt_d9]
  rw [abs_of_pos (lt_trans (by norm_num) hlo)]
  exact ⟨hlo, hhi, hhi.le.trans (by norm_num)⟩

end MetaMathlibExt
