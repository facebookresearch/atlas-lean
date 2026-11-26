/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.DataStructures.LinearProbingSuccessfulSearchCost
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for Knuth's exact mean successful-search cost

These examples cover a single item, two items that may collide, and a full three-cell table.
-/

namespace Cslib.Algorithms.Lean.LinearProbing

example (N : ℕ) (hN : 1 ≤ N) : successfulSearchCost N 1 = 1 := by
  rw [successfulSearchCost_eq N 1 (by decide) hN]
  norm_num [knuthE]

example (N : ℕ) (hN : 2 ≤ N) : successfulSearchCost N 2 = 1 + (1 / N) / 2 := by
  rw [successfulSearchCost_eq N 2 (by decide) hN]
  norm_num [knuthE, Finset.sum_range_succ]
  ring

example : successfulSearchCost 3 3 = 13 / 9 := by
  rw [successfulSearchCost_eq 3 3 (by decide) (by decide)]
  norm_num [knuthE, Finset.sum_range_succ, Nat.descFactorial_succ]

end Cslib.Algorithms.Lean.LinearProbing
