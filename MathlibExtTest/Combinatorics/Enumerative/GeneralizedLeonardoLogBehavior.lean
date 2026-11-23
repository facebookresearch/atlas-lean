/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.GeneralizedLeonardoLogBehavior
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Tests for reciprocal log-balancedness

The sequence `z n = n + 1` satisfies the recurrence with coefficients `3 / 2` and `1 / 2`.
Its initial block starts at zero, and the two inequalities propagate to every positive index.
-/

namespace MetaMathlibExt

example (n : ℕ) (hn : 1 ≤ n) :
    (1 / (n + 1 : ℝ)) ^ 2 ≤ (1 / ((n - 1 : ℕ) + 1 : ℝ)) * (1 / (↑(n + 1) + 1 : ℝ)) ∧
      (1 / ((n - 1 : ℕ) + 1 : ℝ) / (n - 1).factorial) *
        (1 / (↑(n + 1) + 1 : ℝ) / (n + 1).factorial) ≤
          (1 / (n + 1 : ℝ) / n.factorial) ^ 2 := by
  apply inv_logBalanced_of_recurrence_of_initial (3 / 2) (1 / 2) (by norm_num)
    (fun i => (i : ℝ) + 1) (by intro i; positivity) _ 0 _ _ n hn
  · intro i hi
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hi, Nat.cast_ofNat]
    linarith
  · intro i hlo hhi
    interval_cases i <;> norm_num [Nat.factorial]
  · intro i _
    push_cast
    field_simp
    linarith

end MetaMathlibExt
