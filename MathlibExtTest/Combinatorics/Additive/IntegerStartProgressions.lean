/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Int.Interval
import MathlibExt.Combinatorics.Additive.IntegerStartProgressions

open MetaMathlibExt
open scoped Pointwise

-- At zero, the middle term is still in the interval, leaving a one-term exterior tail.
example : ¬ IsMSTDSet (realIntervalSet 3 ∪ realAPSet 0 2 2) := by
  simpa only [Nat.cast_zero, Nat.cast_ofNat] using
    not_isMSTDSet_intervalAP_nat_of_le_sub_one 3 2 2 0 (by decide) (by decide)
      (by decide) (by decide)

-- At the right endpoint with d = n, consecutive blocks of cross-differences just abut.
example : ¬ IsMSTDSet (realIntervalSet 3 ∪ realAPSet 2 2 3) :=
  not_isMSTDSet_intervalAP_nat_of_le_sub_one 3 2 3 2 (by decide) (by decide)
    (by decide) (by decide)

-- At the right endpoint with d > n, the positive cross-differences are separated.
example : ¬ IsMSTDSet (realIntervalSet 3 ∪ realAPSet 2 2 4) :=
  not_isMSTDSet_intervalAP_nat_of_le_sub_one 3 2 4 2 (by decide) (by decide)
    (by decide) (by decide)

-- Closed integer models of the last two unions: the abutting blocks fill the
-- full difference interval, whereas the separated blocks leave gaps.
example : let A : Finset ℤ := {0, 1, 2, 5, 8}; A - A = Finset.Icc (-8) 8 := by decide

example : let A : Finset ℤ := {0, 1, 2, 6, 10};
    (A + A).card = 13 ∧ (A - A).card = 17 := by decide
