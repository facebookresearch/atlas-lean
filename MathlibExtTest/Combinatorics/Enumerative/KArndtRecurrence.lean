/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.KArndtRecurrence

open MetaMathlibExt

-- At weight three the negative-shift correction counts the empty composition for shift -1.
example : (kArndtTotalCount (-1) 3 : ℤ) = 3 := by
  calc
    (kArndtTotalCount (-1) 3 : ℤ) = kArndtTotalCount (-1) 2 + 2 * kArndtTotalCount (-1) 1 - 1 :=
      kArndtTotalCount_recurrence.1 1 3 (by decide)
    _ = 3 := by decide

-- At the same weight the correction for shift -2 is already outside the range.
example : (kArndtTotalCount (-2) 3 : ℤ) = 4 := by
  calc
    (kArndtTotalCount (-2) 3 : ℤ) = kArndtTotalCount (-2) 2 + 2 * kArndtTotalCount (-2) 1 - 0 :=
      kArndtTotalCount_recurrence.1 2 3 (by decide)
    _ = 4 := by decide

-- For shift one the pair (3,1) first contributes at weight four.
example : (kArndtTotalCount 1 3 : ℤ) = 1 ∧ (kArndtTotalCount 1 4 : ℤ) = 2 := by
  constructor
  · exact (kArndtTotalCount_recurrence.2 1 3 (by decide)).trans (by decide)
  · exact (kArndtTotalCount_recurrence.2 1 4 (by decide)).trans (by decide)
