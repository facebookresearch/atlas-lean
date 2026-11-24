/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RingChooseSub

open Finset MetaMathlibExt

-- A single shift recovers the difference of two consecutive binomial coefficients.
example (m n : ℕ) :
    Ring.choose ((n : ℤ) + m - 1) (m + 1) =
      Ring.choose ((n : ℤ) + m) (m + 1) - Ring.choose ((n : ℤ) + m - 1) m := by
  simpa [sum_range_succ, ← add_assoc, sub_eq_add_neg] using ringChoose_sub_eq_sum (m + 1) n 1

-- The upper argument is negative, and the indices 4 and 5 exceed the lower argument.
example : Ring.choose (-3 : ℤ) 3 = -10 := by
  calc
    _ = _ := ringChoose_sub_eq_sum 3 0 5
    _ = -10 := by decide
