/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Prime.Basic
import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfect

namespace MathlibExtTest.NumberTheory.ArithmeticFunction.BiunitaryTriperfect

open MetaMathlibExt

-- A biunitary triperfect number with `3`-exponent at least `3` is divisible by `16`.
example (N : ℕ) (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N)
    (hf : 3 ≤ N.factorization 3) : 16 ∣ N := by
  have h4 := four_le_factorization_two_of_biunitaryTriperfect N hN hσ hf
  have h24 : (2 : ℕ) ^ 4 ∣ N :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hN.ne').mpr h4
  have h216 : (2 : ℕ) ^ 4 = 16 := rfl
  rw [h216] at h24
  exact h24

-- The same conclusion from the divisibility hypothesis `27 ∣ N`.
example (N : ℕ) (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N) (h27 : 27 ∣ N) :
    16 ∣ N := by
  have hf : 3 ≤ N.factorization 3 := by
    have h33 : (3 : ℕ) ^ 3 ∣ N := by
      have h273 : (27 : ℕ) = 3 ^ 3 := rfl
      rw [h273] at h27
      exact h27
    exact (Nat.prime_three.pow_dvd_iff_le_factorization hN.ne').mp h33
  have h4 := four_le_factorization_two_of_biunitaryTriperfect N hN hσ hf
  have h24 : (2 : ℕ) ^ 4 ∣ N :=
    (Nat.prime_two.pow_dvd_iff_le_factorization hN.ne').mpr h4
  have h216 : (2 : ℕ) ^ 4 = 16 := rfl
  rw [h216] at h24
  exact h24

end MathlibExtTest.NumberTheory.ArithmeticFunction.BiunitaryTriperfect
