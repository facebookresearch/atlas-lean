/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.AlzerRichardsSignedStirlingSum
import Mathlib.Tactic.NormNum

open Finset MetaMathlibExt

-- At n = 0 the boundary identity is a first difference, independent of the shift.
example (j : ℕ) :
    (signedStirlingFirst (j + 1) j : ℚ) / (j + 1) -
      (signedStirlingFirst (1 + j + 1) (1 + j) : ℚ) / (1 + j + 1) = 1 / 2 := by
  simpa [sum_range_succ, Nat.choose_one_right, div_eq_mul_inv, sub_eq_add_neg, mul_comm]
    using (sum_choose_div_choose_mul_signedStirlingFirst j 0).2

-- The upper endpoint r = n still gives cancellation among the nonzero terms.
example :
    -(signedStirlingFirst 3 1 : ℚ) + (signedStirlingFirst 4 2 : ℚ) / 2 -
      (signedStirlingFirst 5 3 : ℚ) / 10 = 0 := by
  have h := (sum_choose_div_choose_mul_signedStirlingFirst 0 2).1 2 le_rfl
  norm_num [sum_range_succ, Nat.choose] at h
  linarith
