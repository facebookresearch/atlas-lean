/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Factorization.Basic
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfectFactorizationTwoNeSixOfBiunitaryTriperfect

/-!
# A divisibility consequence of excluding exponent six at two

For a positive biunitary triperfect number divisible by 27, divisibility by 64 implies
divisibility by 128.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 11.
-/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction
namespace BiunitaryTriperfectFactorizationTwoNeSixOfBiunitaryTriperfect

open MetaMathlibExt

example (N : ℕ) (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N)
    (h27 : 27 ∣ N) (h64 : 64 ∣ N) : 128 ∣ N := by
  have h3 : 3 ≤ N.factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization (k := 3) (by decide : Nat.Prime 3) hN.ne').mp h27
  have h2 : 6 ≤ N.factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization (k := 6) Nat.prime_two hN.ne').mp h64
  have hne := factorization_two_ne_six_of_biunitaryTriperfect N hN hσ h3
  exact (Nat.Prime.pow_dvd_iff_le_factorization (k := 7) Nat.prime_two hN.ne').mpr (by omega)

end BiunitaryTriperfectFactorizationTwoNeSixOfBiunitaryTriperfect
end MathlibExtTest.NumberTheory.ArithmeticFunction
