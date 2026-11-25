/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.PrimitivePrimeDivisorPowAddOne
import Mathlib.Data.Nat.Prime.Basic

namespace MetaMathlibExt

-- At index one, an even term with an odd prime factor is allowed.
example : ∃ p, IntegerSequence.IsPrimitivePrimeDivisor (fun m => (5 : ℤ) ^ m + 1) 1 p ∧
    p % 2 = 1 := by
  apply exists_primitivePrimeDivisor_pow_add_one 5 1 (by decide) (by decide) (by decide)
  rintro ⟨_, k, hk⟩
  have hdvd : 3 ∣ 2 ^ k := hk ▸ (by decide : 3 ∣ 5 + 1)
  exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hdvd)

-- At (3, 1), only 2 divides the term as a prime, and it fails the congruence.
example : ¬ ∃ p, IntegerSequence.IsPrimitivePrimeDivisor (fun m => (3 : ℤ) ^ m + 1) 1 p ∧
    p % 2 = 1 := by
  rintro ⟨p, hp, hmod⟩
  have hdvd : p ∣ 2 ^ 2 := Int.natCast_dvd_natCast.mp hp.dvd
  have hp2 := hp.prime.dvd_of_dvd_pow hdvd
  have := (Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp hp2
  omega

-- At (2, 3), the only prime dividing 9 already divides the first term, 3.
example (p : ℕ) : ¬ IntegerSequence.IsPrimitivePrimeDivisor (fun m => (2 : ℤ) ^ m + 1) 3 p := by
  intro hp
  have hdvd : p ∣ 3 ^ 2 := Int.natCast_dvd_natCast.mp hp.dvd
  exact hp.not_dvd_of_lt (s := 1) (by decide) (by decide)
    (Int.natCast_dvd_natCast.mpr (hp.prime.dvd_of_dvd_pow hdvd))

end MetaMathlibExt
