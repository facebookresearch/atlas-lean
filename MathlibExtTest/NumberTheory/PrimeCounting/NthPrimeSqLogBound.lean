/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimeCounting.NthPrimeSqLogBound

/-!
# Endpoint and cutoff tests for the nth-prime inequality
-/

namespace MetaMathlibExt

-- At the first index, the prime is 2.
example :
    118.676119576 * Real.log 2 ^ 3 + 709.7856 * 2 * Real.log 2 ^ 2 <
      937.5 * 2 ^ 2 * Real.log 2 + 5674.5 * 2 ^ 2 := by
  simpa [Nat.nth_prime_zero_eq_two] using nthPrime_sq_log_bound 1 le_rfl

-- The first prime above the cutoff of 64 is the nineteenth prime.
example :
    118.676119576 * 19 ^ 2 * Real.log 67 ^ 3 + 709.7856 * 19 * 67 * Real.log 67 ^ 2 <
      937.5 * 67 ^ 2 * Real.log 67 + 5674.5 * 67 ^ 2 := by
  have hp : Nat.nth Nat.Prime 18 = 67 := by
    rw [show 18 = Nat.count Nat.Prime 67 by decide]
    exact Nat.nth_count (by decide : Nat.Prime 67)
  simpa only [show 19 - 1 = 18 by decide, hp, Nat.cast_ofNat] using
    nthPrime_sq_log_bound 19 (by decide)

end MetaMathlibExt
