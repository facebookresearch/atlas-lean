/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.GaussKuzminSymmetry

/-! # Tests for characteristic numbers of three-digit strings -/

open MetaMathlibExt

-- With final digit two the two characteristic numbers can differ by just one.
example : characteristicNumber [1, 2, 2] = 120 ∧ characteristicNumber [2, 1, 2] = 121 := by
  decide

-- Increasing the final digit to three reverses the order of these values.
example : characteristicNumber [1, 2, 3] = 221 ∧ characteristicNumber [2, 1, 3] = 210 := by
  decide

-- The final digit can coincide with the first, even at the smallest positive digit.
example (b : ℕ) (hb : 1 < b) : characteristicNumber [1, b, 1] ≠ characteristicNumber [b, 1, 1] :=
  characteristicNumber_swap_ne 1 b 1 Nat.one_pos (Nat.zero_lt_of_lt hb) Nat.one_pos hb.ne
