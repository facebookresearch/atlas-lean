/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryPrimeDivisorGeSeven

/-!
# Tests for large prime factors of biunitary divisor sums
-/

open MetaMathlibExt

-- The bound is attained: at the least allowed prime and exponent, the sum is `112 = 16 * 7`.
example : Nat.Prime 7 ∧ 7 ∣ sigmaBiunitary (3 ^ 4) := by decide

example : ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (3 ^ 4) ∧ 7 ≤ q :=
  exists_prime_ge_seven_dvd_sigmaBiunitary_prime_pow 3 4 (by decide) (by decide) (by decide)

-- The public theorem also applies at the next (odd) exponent.
example : ∃ q, q.Prime ∧ q ∣ sigmaBiunitary (3 ^ 5) ∧ 7 ≤ q :=
  exists_prime_ge_seven_dvd_sigmaBiunitary_prime_pow 3 5 (by decide) (by decide) (by decide)
