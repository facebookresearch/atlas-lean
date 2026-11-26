/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FkPerfectIsKLNearPerfectOneTwoMulPrimePow
import Mathlib.Tactic.NormNum

/-! # Tests for near-perfect numbers of the form `2 * p ^ a`

We test the witness `18` and exclude twice a power of the prime `5`.
-/

namespace MathlibExtTest.NumberTheory.FkPerfect

open MathlibExt.NumberTheory.FkPerfectWanted

example : IsKLNearPerfect 1 1 18 :=
  (isKLNearPerfect_one_two_mul_prime_pow 3 2 1 (by decide) (by decide) (by decide)).1

example (a l : ℕ) (hl : 1 ≤ l) : ¬ IsKLNearPerfect 1 l (2 * 5 ^ a) := by
  intro h
  have heq :=
    (isKLNearPerfect_one_two_mul_prime_pow 5 a l (by decide) (by decide) hl).2 h
  have hpow : (5 : ℕ) ^ a = 9 := by omega
  cases a with
  | zero => norm_num at hpow
  | succ a =>
    have hdiv : 5 ∣ (9 : ℕ) := by
      rw [← hpow]
      exact dvd_pow_self 5 (by omega)
    norm_num at hdiv

end MathlibExtTest.NumberTheory.FkPerfect
