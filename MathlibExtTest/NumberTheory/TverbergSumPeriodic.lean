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

-- At modulus zero the full period is empty and the partial sums still admit shifts.
example : (∑ k ∈ Finset.range 0, tverbergSum round ![-1, 1] 0 k) = 0 :=
  ((tverbergPartialSum_vanish_and_periodic (ℓ := 2) (hℓ := by decide) (a := ![-1, 1]) (m := 0)).1
    round (by simp)).1

example : (∑ k ∈ Finset.Icc (1 : ℕ) (2 + 3 * 0), tverbergSum Int.ceil ![-1, 1] 0 k) =
    ∑ k ∈ Finset.Icc (1 : ℕ) 2, tverbergSum Int.ceil ![-1, 1] 0 k :=
  (((tverbergPartialSum_vanish_and_periodic (by decide : 2 ≤ 2) ![-1, 1] 0).2
    Int.ceil (by simp)).2 2 3).1

-- A partial sum can be nonzero even after adding whole periods.
example : (∑ k ∈ Finset.range (0 + 3 * 2 + 1), tverbergSum round ![1, 1] 2 k) = -1 := by
  have h := (tverbergPartialSum_vanish_and_periodic (by decide : 2 ≤ 2) ![1, 1] 2).1 round (by simp)
  rw [(h.2 0 3).1]
  norm_num [sum_at_tie, round_eq]

-- The positive-index tail uses half-down rounding and permits a negative coordinate shift.
example : (∑ k ∈ Finset.Icc (1 : ℕ) 1, tverbergSum (fun y : ℝ ↦ ⌈y - 1 / 2⌉) ![-1, 1] 2 k) =
    ∑ k ∈ Finset.Icc (1 : ℕ) 1, tverbergSum (fun y : ℝ ↦ ⌈y - 1 / 2⌉) ![1, 1] 2 k := by
  have h := (tverbergPartialSum_vanish_and_periodic (by decide : 2 ≤ 2) ![1, 1] 2).2
    (fun y : ℝ ↦ ⌈y - 1 / 2⌉) (by simp)
  have ha : Function.update (![1, 1] : Fin 2 → ℤ) 0 (1 + -1 * 2) = ![-1, 1] := by decide
  rw [← ha]
  exact (h.2 0 0).2 1 0 (-1)

end MetaMathlibExt.tverbergSum_periodic
