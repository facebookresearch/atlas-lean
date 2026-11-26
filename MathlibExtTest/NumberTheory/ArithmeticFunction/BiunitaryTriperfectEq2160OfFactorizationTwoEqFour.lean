/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ArithmeticFunction.BiunitaryTriperfectEq2160OfFactorizationTwoEqFour

/-!
# Tests for the exact exponent-four biunitary triperfect theorem

The number `2160` satisfies the hypotheses. The classification determines the exponent at five
and excludes exponent four at three.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 14.
-/

namespace MathlibExtTest.NumberTheory.ArithmeticFunction
namespace BiunitaryTriperfectEq2160OfFactorizationTwoEqFour

open MetaMathlibExt

private theorem factorization_2160 : (2160 : ℕ).factorization =
    Finsupp.single 2 4 + Finsupp.single 3 3 + Finsupp.single 5 1 := by
  rw [show (2160 : ℕ) = 2 ^ 4 * 3 ^ 3 * 5 by decide,
    Nat.factorization_mul (by decide) (by decide),
    Nat.factorization_mul (by decide) (by decide),
    Nat.prime_two.factorization_pow, (by decide : Nat.Prime 3).factorization_pow,
    (by decide : Nat.Prime 5).factorization]

example : 0 < (2160 : ℕ) ∧ sigmaBiunitary 2160 = 3 * 2160 ∧
    (2160 : ℕ).factorization 2 = 4 ∧ (2160 : ℕ).factorization 3 = 3 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · decide +kernel
  · simp [factorization_2160]
  · simp [factorization_2160]

example (N : ℕ) (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N)
    (he : N.factorization 2 = 4) (h3 : N.factorization 3 = 3) :
    N.factorization 5 = 1 := by
  have h := eq_2160_of_factorization_two_eq_four N hN hσ (by omega) he (by omega)
  rw [h]
  simp [factorization_2160]

example (N : ℕ) (hN : 0 < N) (hσ : sigmaBiunitary N = 3 * N)
    (he : N.factorization 2 = 4) (h3 : N.factorization 3 = 4) : False := by
  have h := eq_2160_of_factorization_two_eq_four N hN hσ (by omega) he (by omega)
  have hf : (2160 : ℕ).factorization 3 = 3 := by simp [factorization_2160]
  rw [h, hf] at h3
  omega

end BiunitaryTriperfectEq2160OfFactorizationTwoEqFour
end MathlibExtTest.NumberTheory.ArithmeticFunction
