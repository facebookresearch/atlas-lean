/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.MaximumNimJosephusIteration

/-! # Tests for `MathlibExt.Combinatorics.MaximumNimJosephusIteration` -/

namespace MathlibExtTest.MaximumNimJosephusIteration

open MetaMathlibExt

example : ∃ p, 1 ≤ p ∧
    Nat.iterate (maximumNimH 2) (p - 1) 1 < 2 ∧
    2 ≤ Nat.iterate (maximumNimH 2) p 1 ∧
    josephus 2 2 = 4 - Nat.iterate (maximumNimH 2) p 1 :=
  josephus_eq_mul_sub_iterate_maximumNimH_pred (k := 2) (n := 2) (hk := by decide) (hn := by decide)

-- For `k = 6`, reaching the threshold for `n = 2` takes three steps: `5 → 7 → 9 → 11`.
example :
    Nat.iterate (maximumNimH 6) 2 5 < 2 * 5 ∧
    2 * 5 ≤ Nat.iterate (maximumNimH 6) 3 5 ∧
    josephus 6 2 = 1 ∧ josephus 6 2 = 2 * 6 - Nat.iterate (maximumNimH 6) 3 5 := by
  decide

-- For `k = 2`, the thresholds for `n = 4` and `n = 5` are both first reached at `7`.
example :
    Nat.iterate (maximumNimH 2) 1 1 < 4 ∧
    5 ≤ Nat.iterate (maximumNimH 2) 2 1 ∧
    josephus 2 4 = 4 * 2 - Nat.iterate (maximumNimH 2) 2 1 ∧
    josephus 2 5 = 5 * 2 - Nat.iterate (maximumNimH 2) 2 1 := by
  decide

end MathlibExtTest.MaximumNimJosephusIteration
