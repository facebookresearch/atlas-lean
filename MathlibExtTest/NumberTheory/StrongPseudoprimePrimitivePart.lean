/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.StrongPseudoprimePrimitivePart

open MetaMathlibExt Polynomial

-- The odd index gives a power equal to one, after removing the intrinsic factor 3.
example : IsStrongPseudoprime 91 (16 : ZMod 91) := by
  refine isStrongPseudoprime_of_dvd_primitivePart (b := 16) (m := 3)
    (by decide) (by decide) (by decide) (Nat.not_prime_mul (a := 7) (b := 13) (by decide)
      (by decide)) (Or.inl ?_)
  have heval : (cyclotomic 3 ℤ).eval 16 = 273 := by
    norm_num [cyclotomic_three, eval_add, eval_pow, eval_X, eval_one]
  change (91 : ℤ) ∣ (cyclotomic 3 ℤ).eval 16 / (Int.gcd ((cyclotomic 3 ℤ).eval 16) 3 : ℤ)
  rw [heval]
  decide

-- The doubled index gives a power equal to minus one, with the same intrinsic factor.
example : IsStrongPseudoprime 91 (17 : ZMod 91) := by
  refine isStrongPseudoprime_of_dvd_primitivePart (b := 17) (m := 3)
    (by decide) (by decide) (by decide) (Nat.not_prime_mul (a := 7) (b := 13) (by decide)
      (by decide)) (Or.inr ?_)
  have heval : (cyclotomic 6 ℤ).eval 17 = 273 := by
    norm_num [cyclotomic_six, eval_add, eval_sub, eval_pow, eval_X, eval_one]
  change (91 : ℤ) ∣ (cyclotomic 6 ℤ).eval 17 / (Int.gcd ((cyclotomic 6 ℤ).eval 17) 3 : ℤ)
  rw [heval]
  decide

-- At a power of two, the intrinsic factor is 2, and the quotient can be a prime square.
example : IsStrongPseudoprime 25 (7 : ZMod 25) := by
  refine isStrongPseudoprime_of_dvd_primitivePart (b := 7) (m := 4)
    (by decide) (by decide) (by decide) (Nat.not_prime_mul (a := 5) (b := 5) (by decide)
      (by decide)) (Or.inl ?_)
  have heval : (cyclotomic 4 ℤ).eval 7 = 50 := by
    rw [show (4 : ℕ) = 2 ^ 2 from rfl,
      cyclotomic_prime_pow_eq_geom_sum (show Nat.Prime 2 by decide)]
    norm_num [Finset.sum_range_succ, eval_add, eval_pow, eval_X, eval_one]
  change (25 : ℤ) ∣ (cyclotomic 4 ℤ).eval 7 / (Int.gcd ((cyclotomic 4 ℤ).eval 7) 4 : ℤ)
  rw [heval]
  decide
