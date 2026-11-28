/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingInsertionCost
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for Knuth's exact mean insertion cost

These cover the smallest table, the first possible collision, and the last free cell.
-/

namespace Cslib.Algorithms.Lean.LinearProbing

example : insertionCost 1 0 = 1 := by
  rw [insertionCost_eq (N := 1) (k := 1) (hk := by decide) (hkN := by decide)]
  norm_num [knuthE, Finset.sum_range_succ]

example (N : ℕ) (hN : 2 ≤ N) : insertionCost N 1 = 1 + 1 / N := by
  rw [insertionCost_eq N 2 (by decide) hN]
  norm_num [knuthE, Finset.sum_range_succ]
  ring

example : insertionCost 7 6 = 4 := by
  rw [insertionCost_eq 7 7 (by decide) (by decide)]
  norm_num [knuthE, Finset.sum_range_succ, Nat.descFactorial_succ, Nat.choose_one_right]

end Cslib.Algorithms.Lean.LinearProbing
