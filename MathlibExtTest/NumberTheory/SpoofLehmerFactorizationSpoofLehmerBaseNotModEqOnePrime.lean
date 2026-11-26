/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SpoofLehmerFactorizationSpoofLehmerBaseNotModEqOnePrime
import Mathlib.Tactic.NormNum

/-! # Tests for primes dividing the evaluation of a spoof Lehmer factorization -/

namespace MathlibExtTest.NumberTheory.SpoofLehmerFactorizationSpoofLehmerBaseNotModEqOnePrime

open MetaMathlibExt

private theorem threeThree_not_trivial : ¬ IsTrivialSpoof (spoofOfBases {3, 3}) := by
  intro h
  have hm : (3, 1) ∈ spoofOfBases {3, 3} := by
    rw [spoofOfBases_three_three]
    simp
  have eq := h (3, 1) hm
  norm_num at eq

private theorem twoTwo_lehmer : IsSpoofLehmer 3 (spoofOfBases {2, 2}) := by
  have hmap : spoofOfBases ({2, 2} : Multiset ℕ) = {(2, 1), (2, 1)} := by
    simp [spoofOfBases]
  rw [hmap]
  refine ⟨by simp [IsSpoofFactorization], by norm_num [spoofEval, spoofTotient], Or.inl (by simp)⟩

private theorem twoTwo_not_trivial : ¬ IsTrivialSpoof (spoofOfBases {2, 2}) := by
  intro h
  have hm : (2, 1) ∈ spoofOfBases {2, 2} := by
    have hmap : spoofOfBases ({2, 2} : Multiset ℕ) = {(2, 1), (2, 1)} := by
      simp [spoofOfBases]
    rw [hmap]
    simp
  have eq := h (2, 1) hm
  norm_num at eq

private theorem twoTwo_not_odd : ¬ IsOddSpoof (spoofOfBases {2, 2}) := by
  intro h
  have hm : (2, 1) ∈ spoofOfBases {2, 2} := by
    have hmap : spoofOfBases ({2, 2} : Multiset ℕ) = {(2, 1), (2, 1)} := by
      simp [spoofOfBases]
    rw [hmap]
    simp
  have eq := h (2, 1) hm
  exact absurd eq (by decide)

-- The prime `3` divides the evaluation `9` of `3 · 3`, so no base is `1` mod `3`.
example : ¬ 3 ≡ 1 [MOD 3] := by
  have hL : IsSpoofLehmer 2 (spoofOfBases {3, 3}) := by
    rw [spoofOfBases_three_three]
    exact isSpoofLehmer_three_three
  have hdvd : ((3 : ℕ) : ℤ) ∣ spoofEval (spoofOfBases {3, 3}) := by
    rw [spoofOfBases_three_three, spoofEval_spoofTotient_three_three.1]
    decide
  exact (spoofLehmer_base_not_modEq_one_prime {3, 3} 2 hL threeThree_not_trivial).1
    3 Nat.prime_three hdvd 3 (by simp)

-- The factorization `2 · 2` is an even `3`-Lehmer factorization, so all bases are even.
example : ∀ a ∈ ({2, 2} : Multiset ℕ), Even a :=
  (spoofLehmer_base_not_modEq_one_prime {2, 2} 3 twoTwo_lehmer twoTwo_not_trivial).2
    twoTwo_not_odd

example : ¬ 3 ≡ 1 [MOD 3] := by decide

example : ∀ a ∈ ({2, 2} : Multiset ℕ), Even a := by decide

end MathlibExtTest.NumberTheory.SpoofLehmerFactorizationSpoofLehmerBaseNotModEqOnePrime
