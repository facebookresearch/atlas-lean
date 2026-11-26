/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsLucasStepOffsetSuryFibSum
import Mathlib.Tactic.NormNum

namespace MathlibExtTest.NumberTheory.Recurrences.SuryIdentityExtensionsLucasStepOffsetSuryFibSum

open MathlibExt.NumberTheory.Recurrences.SuryIdentityExtensionsWanted

-- At step two with offset one the weight is `-1` and the denominators are `1`.
example (n : ℕ) :
    fibAtInt (2 * ((n : ℤ) + 1)) =
      ∑ i ∈ Finset.range (n + 1), (-1 : ℚ) ^ (n - i) * lucasAtInt (2 * (i : ℤ) + 1) := by
  have h := lucas_step_offset_sury_fib_sum 2 1 n (by decide)
  simpa only [Nat.cast_ofNat, show fibAtInt 2 = 1 by decide,
    show lucasAtInt 1 = 1 by decide, show (2 : ℤ) - 1 = 1 by decide,
    zpow_one, div_one, one_mul, mul_one] using h

-- At step two with offset minus one the weight is `4` and the outer factor is `1 / -1`.
example (n : ℕ) :
    fibAtInt (2 * ((n : ℤ) + 1)) =
      (1 / (-1 : ℚ)) *
        ∑ i ∈ Finset.range (n + 1),
          ((4 : ℚ)) ^ (n - i) * lucasAtInt (2 * (i : ℤ) + -1) := by
  have h := lucas_step_offset_sury_fib_sum 2 (-1) n (by decide)
  simpa only [Nat.cast_ofNat, show fibAtInt 2 = 1 by decide,
    show lucasAtInt (-1) = -1 by decide +kernel,
    show (2 : ℤ) - (-1) = 3 by decide, show lucasAtInt 3 = 4 by decide,
    show ((-1 : ℚ) ^ (-1 : ℤ)) = -1 by simp,
    show ((-1 : ℚ) * 4 / -1) = 4 by norm_num] using h

end MathlibExtTest.NumberTheory.Recurrences.SuryIdentityExtensionsLucasStepOffsetSuryFibSum
