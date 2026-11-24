/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.FieldTheory.Finite.MonomialPermutationPolynomial
import Mathlib.FieldTheory.Finite.Basic

namespace MetaMathlibExt.MonomialPermutationPolynomialTest

open Polynomial

/-- `7` is prime, so `ZMod 7` is a field. -/
instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by decide⟩

-- `gcd(5, 7 - 1) = 1`, so `X ^ 5` permutes `ZMod 7`.
example : (X ^ 5 : (ZMod 7)[X]).IsPermutationPolynomial := by
  rw [isPermutationPolynomial_X_pow_iff_coprime (by norm_num), ZMod.card]
  decide

-- `gcd(3, 7 - 1) = 3`, so `X ^ 3` does not permute `ZMod 7`.
example : ¬(X ^ 3 : (ZMod 7)[X]).IsPermutationPolynomial := by
  rw [isPermutationPolynomial_X_pow_iff_coprime (by norm_num), ZMod.card]
  decide

-- The collision behind the previous example: `2 ^ 3 = 8 = 1 ^ 3` in `ZMod 7`.
example : (X ^ 3 : (ZMod 7)[X]).eval 2 = (X ^ 3 : (ZMod 7)[X]).eval 1 := by
  simp only [eval_pow, eval_X]
  decide

-- With two elements `q - 1 = 1`, so every monomial of positive degree is a permutation
-- polynomial.
example {d : ℕ} (hd : 0 < d) : (X ^ d : (ZMod 2)[X]).IsPermutationPolynomial := by
  rw [isPermutationPolynomial_X_pow_iff_coprime hd, ZMod.card]
  exact Nat.coprime_one_right d

-- The monomial `X ^ q` permutes every finite field with `q` elements.
example {K : Type*} [Field K] [Fintype K] :
    (X ^ Fintype.card K : K[X]).IsPermutationPolynomial := by
  rw [isPermutationPolynomial_X_pow_iff_coprime Fintype.card_pos,
    Nat.coprime_self_sub_right Fintype.card_pos]
  exact Nat.coprime_one_right _

-- Squaring permutes a finite field of characteristic `2` ...
example {K : Type*} [Field K] [Fintype K] (hK : ringChar K = 2) :
    (X ^ 2 : K[X]).IsPermutationPolynomial := by
  rw [isPermutationPolynomial_X_pow_iff_coprime two_pos, Nat.coprime_two_left, Nat.odd_iff]
  have hq := FiniteField.even_card_iff_char_two.mp hK
  have hpos : 0 < Fintype.card K := Fintype.card_pos
  omega

-- ... and no finite field of odd characteristic.
example {K : Type*} [Field K] [Fintype K] (hK : ringChar K ≠ 2) :
    ¬(X ^ 2 : K[X]).IsPermutationPolynomial := by
  rw [isPermutationPolynomial_X_pow_iff_coprime two_pos, Nat.coprime_two_left, Nat.odd_iff]
  have hq := FiniteField.odd_card_of_char_ne_two hK
  omega

end MetaMathlibExt.MonomialPermutationPolynomialTest
