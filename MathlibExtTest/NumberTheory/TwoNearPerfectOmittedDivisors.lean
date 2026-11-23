/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.TwoNearPerfectOmittedDivisors

namespace MetaMathlibExt

-- The omitted pair (2, 1) at 18 realizes the even-first order.
example : ((2 + 1 : ℕ) : ℤ) = 3 ∧ (2 : ℕ) % 2 ≠ 1 % 2 :=
  omitted_divisors_sum_two_pow_mul_prime_sq (k := 1) Nat.prime_three (by decide)
    (by decide) (by decide) (by decide) (by decide)

-- At 36, omitting 1 forces the other divisor to be 18 and hence even.
example {d : ℕ} (hd : d ∣ 36) (hne : 1 ≠ d)
    (hσ : ArithmeticFunction.sigma 1 36 = 2 * 36 + 1 + d) : d = 18 ∧ d % 2 = 0 := by
  obtain ⟨hsum, hparity⟩ := omitted_divisors_sum_two_pow_mul_prime_sq
    (k := 2) Nat.prime_three (by decide) (one_dvd _) hd hne hσ
  norm_num at hsum hparity
  omega

end MetaMathlibExt
