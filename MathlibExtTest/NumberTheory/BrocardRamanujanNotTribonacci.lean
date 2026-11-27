/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.BrocardRamanujanNotTribonacci

open MetaMathlibExt

-- The theorem applied at arbitrary indices.
example (m n : ℕ) : Nat.factorial m + 1 ≠ tribonacci n ^ 2 :=
  brocardRamanujan_not_tribonacci m n

-- The factorial-plus-one values at the known Brocard indices are not
-- Tribonacci squares: 5, 11 and 71 are not Tribonacci numbers.
example : Nat.factorial 4 + 1 ≠ tribonacci 6 ^ 2 :=
  brocardRamanujan_not_tribonacci 4 6

example : Nat.factorial 5 + 1 ≠ tribonacci 7 ^ 2 :=
  brocardRamanujan_not_tribonacci 5 7

example : Nat.factorial 7 + 1 ≠ tribonacci 10 ^ 2 :=
  brocardRamanujan_not_tribonacci 7 10

example : ¬ ∃ m n : ℕ, Nat.factorial m + 1 = tribonacci n ^ 2 := by
  rintro ⟨m, n, h⟩
  exact brocardRamanujan_not_tribonacci m n h

-- The negative-index value that shows why nonnegative indices matter.
example : tribonacciInt (-10) = 5 :=
  tribonacciInt_neg_ten

#print axioms MetaMathlibExt.brocardRamanujan_not_tribonacci
