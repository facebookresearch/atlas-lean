/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminSymmetry

/-! # Tests for convergent matrices and characteristic numbers -/

open MetaMathlibExt

-- Appending to the empty string gives the single digit matrix.
example (t : ℕ) (ht : 1 ≤ t) : convergentMatrix [t] = !![0, 1; 1, (t : ℤ)] := by
  simpa [convergentMatrix_nil] using
    (convergentMatrix_reverse_append_cons [] (by simp) t ht).2.1

-- Distinct digits give unequal off-diagonal entries and distinguish the two multiplication orders.
example :
    convergentMatrix [3, 2] = !![1, 2; 3, 7] ∧
    convergentMatrix [2, 3, 1] = !![3, 4; 7, 9] ∧
    convergentMatrix [1, 2, 3] = !![2, 7; 3, 10] ∧
    convergentMatrix [1, 3, 2] = !![3, 7; 4, 9] := by
  have h : convergentMatrix [2, 3] = !![1, 3; 2, 7] := by decide
  simpa [h] using convergentMatrix_reverse_append_cons [2, 3] (by decide) 1 (by decide)

-- With final digit two the two characteristic numbers can differ by just one.
example : characteristicNumber [1, 2, 2] = 120 ∧ characteristicNumber [2, 1, 2] = 121 := by
  decide

-- Increasing the final digit to three reverses the order of these values.
example : characteristicNumber [1, 2, 3] = 221 ∧ characteristicNumber [2, 1, 3] = 210 := by
  decide

-- The final digit can coincide with the first, even at the smallest positive digit.
example (b : ℕ) (hb : 1 < b) : characteristicNumber [1, b, 1] ≠ characteristicNumber [b, 1, 1] :=
  characteristicNumber_swap_ne 1 b 1 Nat.one_pos (Nat.zero_lt_of_lt hb) Nat.one_pos hb.ne
