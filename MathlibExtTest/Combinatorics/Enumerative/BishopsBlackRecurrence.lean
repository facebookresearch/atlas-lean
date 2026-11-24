/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.NonattackingBishopsAnassas

open MetaMathlibExt

-- On odd and even boards the positive coefficients are 1 and 3, respectively.
example : (bishopsBlack 3 2 : ℤ) = bishopsBlack 2 2 + 1 * bishopsBlack 2 1 :=
  (bishopsBlack_recurrence 2 1).1

example : (bishopsBlack 4 2 : ℤ) = bishopsBlack 3 2 + 3 * bishopsBlack 3 1 :=
  (bishopsBlack_recurrence 3 1).1

example : bishopsBlack 3 2 = 2 ∧ bishopsBlack 4 2 = 14 := by decide +kernel

example : bishopsBlack 0 0 = 1 := (bishopsBlack_recurrence 0 0).2.1
example : bishopsBlack 4 0 = 1 := (bishopsBlack_recurrence 4 0).2.1
example : bishopsBlack 0 2 = 0 := (bishopsBlack_recurrence 0 1).2.2

-- At and beyond the column limit the coefficient is zero and then negative.
example : (bishopsBlack 3 3 : ℤ) = bishopsBlack 2 3 + 0 * bishopsBlack 2 2 :=
  (bishopsBlack_recurrence 2 2).1

example : (bishopsBlack 3 4 : ℤ) = bishopsBlack 2 4 + (-1) * bishopsBlack 2 3 :=
  (bishopsBlack_recurrence 2 3).1

example : bishopsBlack 2 3 = 0 ∧ bishopsBlack 3 4 = 0 := by decide +kernel
