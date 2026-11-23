/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RoundQuotientOddCount

/-!
# Tests for the rounding sequence parity count
-/

open MetaMathlibExt

-- At zero the interval of denominators is empty.
example : roundQuotientOddCount 0 = 0 := by decide

-- At one the first floor term is two and the correction subtracts one.
example : (roundQuotientOddCount 1 : ℤ) = 1 := by
  rw [roundQuotientOddCount_eq_alternating_sum]
  decide

-- For n = 5 the half-integer 5/2 rounds up to the odd integer 3.
example : roundQuotientOddCount 5 = 4 := by decide +kernel
