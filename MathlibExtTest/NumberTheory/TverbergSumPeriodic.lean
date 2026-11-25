/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TverbergSumPeriodic
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.tverbergSum_periodic

private theorem sum_at_tie (F : ℝ → ℤ) :
    tverbergSum F ![1, 1] 2 0 = F 0 - 2 * F (1 / 2) + F 1 := by
  have hsets : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [tverbergSum, hsets, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [Finset.sum_insert]
  ring

-- In the minimum dimension, a negative period preserves the nonzero sum at a rounding tie.
example : tverbergSum round ![1, 1] 2 (-2) = -1 := by
  have h := (tverbergSum_periodic (by decide : 2 ≤ 2) round (by simp)
    ![1, 1] 2 0 0 (-1)).2
  calc
    _ = tverbergSum round ![1, 1] 2 0 := by simpa using h
    _ = -1 := by norm_num [sum_at_tie, round_eq]

-- With ties rounded down the sum has the opposite sign, even after shifting one entry.
example : tverbergSum (fun x : ℝ ↦ ⌈x - 1 / 2⌉) ![-1, 1] 2 0 = 1 := by
  have h := (tverbergSum_periodic (by decide : 2 ≤ 2) (fun x : ℝ ↦ ⌈x - 1 / 2⌉)
    (by simp) ![1, 1] 2 0 0 (-1)).1
  have ha : Function.update (![1, 1] : Fin 2 → ℤ) 0 (1 + -1 * 2) = ![-1, 1] := by decide
  calc
    _ = tverbergSum (fun x : ℝ ↦ ⌈x - 1 / 2⌉) ![1, 1] 2 0 := by
      rw [← ha]
      exact h
    _ = 1 := by norm_num [sum_at_tie]

-- Below the dimension bound, a coordinate shift by the modulus can change the sum.
example : tverbergSum Int.floor ![-1] 2 0 ≠ tverbergSum Int.floor ![1] 2 0 := by
  norm_num [tverbergSum_one]

end MetaMathlibExt.tverbergSum_periodic
