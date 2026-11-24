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

-- At i = n + 1 the outer interval is empty, leaving just the term with m = 0.
example (n : ℕ) (hn : 1 ≤ n) :
    (∑ m ∈ range (n + 2 - (n + 1)),
      (n - m - 1).choose (n + 1 - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1))) = 1 := by
  rw [sum_choose_mul_fib_odd_eq_choose_add_sum n (n + 1) hn (by omega) le_rfl]
  simp [show n + 1 - 2 = n - 1 by omega]

-- At n = 5 and i = 3 the isolated term is 4 and the three inner sums are 7, 4 and 1.
example : (∑ m ∈ range (5 + 2 - 3),
    (5 - m - 1).choose (3 - 2) * (if m = 0 then 1 else Nat.fib (2 * m - 1))) = 16 := by
  rw [sum_choose_mul_fib_odd_eq_choose_add_sum 5 3 (by decide) (by decide) (by decide)]
  decide
