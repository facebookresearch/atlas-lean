/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RepetendTable.OrderCount

/-! # Tests for the number of units of a given order -/

open MetaMathlibExt

-- At order zero the divisibility statement forces the count itself to vanish.
example (n : ℕ) [NeZero n] :
    (Finset.univ.filter fun u : (ZMod n)ˣ => orderOf u = 0).card = 0 := by
  simpa only [Nat.totient_zero, zero_dvd_iff] using totient_dvd_card_orderOf_eq 0 n

-- The noncyclic unit group modulo 16 has twice as many units of order four as a cyclic
-- group of order four does.
example : (Finset.univ.filter fun u : (ZMod 16)ˣ => orderOf u = 4).card = 2 * Nat.totient 4 := by
  calc
    _ = (Finset.univ.filter fun u : (ZMod 16)ˣ =>
        u ^ 4 = 1 ∧ ∀ m < 4, 0 < m → u ^ m ≠ 1).card := by
      congr 1
      exact Finset.filter_congr fun _ _ ↦ orderOf_eq_iff (by decide)
    _ = _ := by decide
