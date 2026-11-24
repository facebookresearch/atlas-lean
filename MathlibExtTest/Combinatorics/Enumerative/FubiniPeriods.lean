/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.FubiniPeriods

open ArithmeticFunction MetaMathlibExt

-- Modulo one, every shift is an eventual period, including zero.
example (p : ℕ) : ∃ N, ∀ n ≥ N, fubiniNumber (n + p) ≡ fubiniNumber n [MOD 1] :=
  (fubiniNumber_eventuallyPeriodic_iff_carmichael_dvd 1 odd_one p).mpr (by simp)

-- The period two modulo three fails to lift to an eventual period modulo nine.
example : ¬ ∃ N, ∀ n ≥ N, fubiniNumber (n + 2) ≡ fubiniNumber n [MOD 9] := by
  rw [fubiniNumber_eventuallyPeriodic_iff_carmichael_dvd 9 (by decide),
    show 9 = 3 ^ (1 + 1) by decide, carmichael_pow_of_prime_ne_two _ Nat.prime_three (by decide),
    Nat.totient_prime_pow_succ Nat.prime_three]
  decide

-- Combining nine and five gives least period lcm(6, 4) = 12.
example (p : ℕ) : (∃ N, ∀ n ≥ N, fubiniNumber (n + p) ≡ fubiniNumber n [MOD 45]) ↔ 12 ∣ p := by
  rw [fubiniNumber_eventuallyPeriodic_iff_carmichael_dvd 45 (by decide),
    show 45 = 3 ^ (1 + 1) * 5 by decide, carmichael_mul (by decide),
    carmichael_of_prime (by decide : Nat.Prime 5),
    carmichael_pow_of_prime_ne_two _ Nat.prime_three (by decide),
    Nat.totient_prime_pow_succ Nat.prime_three]
  rfl
