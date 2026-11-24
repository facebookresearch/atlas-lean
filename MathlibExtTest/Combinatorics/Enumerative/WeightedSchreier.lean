/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.WeightedSchreier

/-! # Tests for weighted Schreier counts and partial sums -/

open MetaMathlibExt

-- Only the empty set fits below 1. At the first positive bound, {1} also qualifies.
example : weightedSchreierCount 1 0 = 1 := by decide
example : weightedSchreierCount 1 1 = 2 := weightedSchreierCount_one 0

-- At bound 5, {3, 4} is admissible while {2, 4} fails the strict cardinality bound.
example : weightedSchreierCount 1 5 = 9 := by decide
example (l : ℕ) : weightedSchreierCount 1 (l + 1) = Nat.fib (l + 2) + 1 := by
  simpa [Nat.add_comm 1 l] using weightedSchreierCount_one l

-- For any positive k the empty interval contributes only the empty set.
example {k : ℕ} (hk : 0 < k) : weightedSchreierCount k 0 = 1 :=
  weightedSchreierCount_of_lt hk

-- At bound 4, moving the zero-weight element into the interval changes the count.
example : weightedSchreierCount 5 4 = 5 := weightedSchreierCount_of_lt (by decide)
example : weightedSchreierCount 4 4 = 6 := by decide

-- A second iteration uses both seed entries. The zero seed gives ordinary iterated sums.
example : seededPartialSums (fun j => j + 3) (fun _ => 2) 2 3 = 19 := by decide
example : iteratedPartialSum 2 (fun _ => (2 : ℕ)) 3 = 6 := by decide

-- At depth two, the first nonzero shifted sum occurs at index two.
example : iteratedPartialSum 2 (fun n => Nat.fib (n + 2)) 2 = 1 := by
  rw [iteratedPartialSum_fib_add_two]
  decide

-- At index four both unshifted terms contribute.
example : iteratedPartialSum 2 (fun n => Nat.fib (n + 2)) 4 = 10 := by
  rw [iteratedPartialSum_fib_add_two]
  decide

-- Negative input terms do not change the shift at positive depth.
example : iteratedPartialSum 3 (fun n => -(n : ℤ) + 1) 5 -
    iteratedPartialSum 3 (fun n => -(n : ℤ)) 5 = 10 := by
  rw [iteratedPartialSum_add_one_sub (fun n => -(n : ℤ))]
  decide

-- With more iterations than input terms, both strict partial sums vanish.
example : iteratedPartialSum 4 (fun n => -(n : ℤ) + 1) 2 -
    iteratedPartialSum 4 (fun n => -(n : ℤ)) 2 = 0 := by
  rw [iteratedPartialSum_add_one_sub (fun n => -(n : ℤ))]
  decide
