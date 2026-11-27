/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.FibonacciStepSuryIdentity

namespace MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

-- At `n = 0`, the negative index has the opposite sign for even and odd steps.
example (j : ℕ) (hj : 1 ≤ j) :
    lucasAtInt j * fibAtInt (-(j : ℤ)) + (-1 : ℚ) ^ j * fibAtInt (2 * (j : ℤ)) = 0 := by
  simpa only [Nat.cast_zero, zero_add, zero_sub, mul_one, mul_neg, pow_one, Finset.sum_range_one,
    mul_zero, show fibAtInt 0 = 0 by rfl] using (fib_step_sury_sum (j := j) (n := 0) (hj := hj))

-- With an odd step the two nonzero summands have opposite signs: `-8 + 128`.
example :
    (∑ i ∈ Finset.range (2 + 1),
      (-1 : ℚ) ^ (3 * (2 + i)) * lucasAtInt 3 ^ i * fibAtInt (3 * (i : ℤ))) = 120 := by
  calc
    _ = _ := (fib_step_sury_sum 3 2 (by decide)).symm
    _ = 120 := by decide +kernel

-- With an even step all the signs are positive: `3 + 27 + 216`.
example :
    (∑ i ∈ Finset.range (3 + 1),
      (-1 : ℚ) ^ (2 * (3 + i)) * lucasAtInt 2 ^ i * fibAtInt (2 * (i : ℤ))) = 246 := by
  calc
    _ = _ := (fib_step_sury_sum 2 3 (by decide)).symm
    _ = 246 := by decide +kernel

end MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted
