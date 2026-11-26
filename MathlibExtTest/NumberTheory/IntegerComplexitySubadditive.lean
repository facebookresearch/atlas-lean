/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import MathlibExt.NumberTheory.IntegerComplexitySubadditive

open MathlibExt.NumberTheory.IntegerComplexityWanted

-- Its value at zero makes the subadditivity inequality fail for the sum 0 + 1.
private def stepBound (n : ℕ) : ℝ :=
  if n = 0 then -1 else if n = 1 then 1 else 2

private theorem stepBound_le_add (k n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    stepBound k ≤ stepBound n + stepBound m := by
  simp only [stepBound, ite_eq_right (Nat.ne_of_gt hn), ite_eq_right (Nat.ne_of_gt hm)]
  split_ifs <;> norm_num

private theorem stepBound_le_cx (n : ℕ) (hn : 1 ≤ n) : stepBound n ≤ (cx n : ℝ) :=
  le_complexity_of_subadditive stepBound (by norm_num [stepBound])
    (fun a b => stepBound_le_add (a + b) a b) (fun a b => stepBound_le_add (a * b) a b) n hn

-- The criterion applies at the smallest positive input.
example : (1 : ℝ) ≤ cx 1 := by
  simpa [stepBound] using stepBound_le_cx 1 (by decide)

-- At two, the nonconstant bound certifies that a single one is not enough.
example : (2 : ℝ) ≤ cx 2 := by
  simpa [stepBound] using stepBound_le_cx 2 (by decide)
