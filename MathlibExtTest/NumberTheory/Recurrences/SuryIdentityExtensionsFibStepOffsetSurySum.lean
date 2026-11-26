/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsFibStepOffsetSurySum

namespace MathlibExtTest.NumberTheory.Recurrences.SuryIdentityExtensionsFibStepOffsetSurySum

-- At step two with offset one the weight is 1: the odd-indexed Fibonacci numbers below
-- `2 * (n + 1)` sum to the Fibonacci number at `2 * (n + 1)`.
open MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted in
example (n : ℕ) :
    fibAtInt (2 * ((n : ℤ) + 1)) =
      ∑ i ∈ Finset.range (n + 1), fibAtInt (2 * (i : ℤ) + 1) := by
  simpa only [Nat.cast_ofNat, show fibAtInt 2 = 1 by decide +kernel,
    show fibAtInt 1 = 1 by decide +kernel,
    show fibAtInt ((2 : ℤ) - 1) = 1 by decide +kernel,
    show (-1 : ℚ) ^ ((1 : ℤ) + 1) = 1 by decide, div_one, mul_one, one_pow,
    one_mul] using (fib_step_offset_sury_sum 2 1 n (by decide) (by decide))

-- At step three with offset two the weight is -1, giving an alternating sum.
open MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted in
example (n : ℕ) :
    fibAtInt (3 * ((n : ℤ) + 1)) =
      2 * ∑ i ∈ Finset.range (n + 1),
        (-1 : ℚ) ^ (n - i) * fibAtInt (3 * (i : ℤ) + 2) := by
  simpa only [Nat.cast_ofNat, show fibAtInt 3 = 2 by decide +kernel,
    show fibAtInt 2 = 1 by decide +kernel,
    show fibAtInt ((3 : ℤ) - 2) = 1 by decide +kernel,
    show (-1 : ℚ) ^ ((2 : ℤ) + 1) = -1 by decide, div_one,
    mul_one] using (fib_step_offset_sury_sum 3 2 n (by decide) (by decide))

end MathlibExtTest.NumberTheory.Recurrences.SuryIdentityExtensionsFibStepOffsetSurySum
