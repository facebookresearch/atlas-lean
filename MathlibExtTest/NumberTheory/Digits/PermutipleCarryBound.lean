/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.PermutipleCarryBound

open MetaMathlibExt

-- Apply the public theorem to every digit index of 87912 = 4 * 21978.
example (j : Fin 5) : permutipleCarry 4 10 (k := 4) ![2, 1, 9, 7, 8] Fin.revPerm j ≤ 3 :=
  permutipleCarry_le 4 10 (by decide) _ _ isPermutiple_87912 j

-- The bound is attained at the third carry of the same permutiple.
example : permutipleCarry 4 10 (k := 4) ![2, 1, 9, 7, 8] Fin.revPerm 3 = 3 := by
  decide

-- At multiplier zero, the bound forces even a successor carry to be zero.
example : permutipleCarry 0 2 (k := 1) (fun _ => 0) Fin.revPerm 1 = 0 := by
  have hp : IsPermutiple 0 2 (k := 1) (fun _ => 0) Fin.revPerm := by
    unfold IsPermutiple
    decide
  exact Nat.le_zero.mp (permutipleCarry_le 0 2 (by decide) _ _ hp 1)

-- At multiplier one and base two, nonzero digits still produce no carry.
example : permutipleCarry 1 2 (k := 1) ![1, 1] Fin.revPerm 1 = 0 := by
  have hp : IsPermutiple 1 2 (k := 1) ![1, 1] Fin.revPerm := by
    unfold IsPermutiple
    decide
  exact Nat.le_zero.mp (permutipleCarry_le 1 2 (by decide) _ _ hp 1)
