/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.GaussianIntPrimeClassification

import Mathlib.Tactic

namespace MetaMathlibExt

open GaussianInt

-- `2 + i` is prime in `ℤ[i]`: its norm is the rational prime `5`.
example : Prime (⟨2, 1⟩ : GaussianInt) :=
  gaussianInt_prime_of_natAbs_norm_prime (by decide)

-- `1 + 2 * i` is prime in `ℤ[i]`: its norm is also `5`.
example : Prime (⟨1, 2⟩ : GaussianInt) :=
  gaussianInt_prime_of_natAbs_norm_prime (by decide)

-- The rational prime `3 ≡ 3 (mod 4)` stays prime in `ℤ[i]`.
example : Prime ((3 : ℕ) : GaussianInt) :=
  (@GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 3 ⟨by norm_num⟩).mpr
    (by norm_num)

-- The rational prime `5 ≡ 1 (mod 4)` does not stay prime in `ℤ[i]`.
example : ¬Prime ((5 : ℕ) : GaussianInt) := by
  rw [@GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 5 ⟨by norm_num⟩]
  decide

-- Splitting of `5`: the classification's second case is witnessed by
-- `a = 2, b = 1, p = 5` for the prime `2 + i`.
example :
    ∃ a b p : ℕ, p.Prime ∧ p % 4 = 1 ∧ a ^ 2 + b ^ 2 = p ∧
      (Associated (⟨2, 1⟩ : GaussianInt) (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∨
        Associated (⟨2, 1⟩ : GaussianInt) (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt)) :=
  ⟨2, 1, 5, by norm_num, by norm_num, by norm_num, Or.inl (Associated.refl _)⟩

-- Splitting of `5` and `13` in the `a, b` form.
example : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 5 ∧
    Prime (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∧
      Prime (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt) :=
  @gaussianInt_split_prime_sq_add_sq 5 ⟨by norm_num⟩ (by norm_num)

example : ∃ a b : ℕ, a ^ 2 + b ^ 2 = 13 ∧
    Prime (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∧
      Prime (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt) :=
  @gaussianInt_split_prime_sq_add_sq 13 ⟨by norm_num⟩ (by norm_num)

-- Alternate sum-of-two-squares presentations can give associated factors:
-- `(1 - 2 * i) * i = 2 + i`.
example : Associated (⟨1, -2⟩ : GaussianInt) (⟨2, 1⟩ : GaussianInt) :=
  ⟨⟨⟨0, 1⟩, ⟨0, -1⟩, by decide, by decide⟩, by decide⟩

-- The classification applied to the three kinds of Gaussian prime:
-- `3`, `2 + i`, and `1 + i`.
example :
    (∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧
      Associated ((3 : ℕ) : GaussianInt) (p : GaussianInt)) ∨
      (∃ a b p : ℕ, p.Prime ∧ p % 4 = 1 ∧ a ^ 2 + b ^ 2 = p ∧
        (Associated ((3 : ℕ) : GaussianInt) (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∨
          Associated ((3 : ℕ) : GaussianInt) (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt))) ∨
      Associated ((3 : ℕ) : GaussianInt) (⟨1, 1⟩ : GaussianInt) :=
  gaussianInt_prime_associated _
    ((@GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime 3 ⟨by norm_num⟩).mpr
      (by norm_num))

example :
    (∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧
      Associated (⟨2, 1⟩ : GaussianInt) (p : GaussianInt)) ∨
      (∃ a b p : ℕ, p.Prime ∧ p % 4 = 1 ∧ a ^ 2 + b ^ 2 = p ∧
        (Associated (⟨2, 1⟩ : GaussianInt) (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∨
          Associated (⟨2, 1⟩ : GaussianInt) (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt))) ∨
      Associated (⟨2, 1⟩ : GaussianInt) (⟨1, 1⟩ : GaussianInt) :=
  gaussianInt_prime_associated _ (gaussianInt_prime_of_natAbs_norm_prime (by decide))

example :
    (∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧
      Associated (⟨1, 1⟩ : GaussianInt) (p : GaussianInt)) ∨
      (∃ a b p : ℕ, p.Prime ∧ p % 4 = 1 ∧ a ^ 2 + b ^ 2 = p ∧
        (Associated (⟨1, 1⟩ : GaussianInt) (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∨
          Associated (⟨1, 1⟩ : GaussianInt) (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt))) ∨
      Associated (⟨1, 1⟩ : GaussianInt) (⟨1, 1⟩ : GaussianInt) :=
  gaussianInt_prime_associated _ gaussianInt_prime_one_add_I

#print axioms GaussianInt.gaussianInt_prime_associated
#print axioms GaussianInt.gaussianInt_split_prime_sq_add_sq

end MetaMathlibExt
