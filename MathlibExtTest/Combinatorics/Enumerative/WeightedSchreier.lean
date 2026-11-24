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

-- A second iteration uses both seed entries. The zero seed gives ordinary iterated sums.
example : seededPartialSums (fun j => j + 3) (fun _ => 2) 2 3 = 19 := by decide
example : iteratedPartialSum 2 (fun _ => (2 : ℕ)) 3 = 6 := by decide
