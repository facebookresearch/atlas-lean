/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.CatalanWordsCapacity

open MetaMathlibExt Finset

-- At the lower bound, the only term uses the convention F_{-1} = 1.
example : (∑ j ∈ Icc 1 1, ∑ m ∈ range (1 - j + 1),
    (1 - m - 1).choose (j - 1) * (if m = 0 then 1 else Nat.fib (2 * m - 1))) = 1 := by
  rw [← fib_two_mul_eq_sum_sum_choose_mul_fib_odd 1 (by decide)]
  rfl

-- For n = 3 the three inner sums are 4, 3 and 1.
example : ((List.range 3).map fun i =>
    ∑ m ∈ range (3 - (i + 1) + 1),
      (3 - m - 1).choose i * (if m = 0 then 1 else Nat.fib (2 * m - 1))) = [4, 3, 1] := by
  decide
