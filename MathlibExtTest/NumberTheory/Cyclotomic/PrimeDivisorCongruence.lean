/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Cyclotomic.PrimeDivisorCongruence
import Mathlib.Tactic.NormNum.DivMod

/-! # Tests for prime divisors of cyclotomic values -/

namespace MetaMathlibExt

open Polynomial

-- The prime divisor 7 of Φ₃(4) = 21 satisfies the congruence.
example : Nat.ModEq 3 7 1 :=
  prime_modEq_one_of_dvd_cyclotomic_eval (x := 4) (by decide) (by decide) (by decide)
    (by decide) (by norm_num [cyclotomic_three])

-- The same value also has the divisor 3, which shows why the primes must be distinct.
example : (3 : ℤ) ∣ (cyclotomic 3 ℤ).eval 4 ∧ ¬ Nat.ModEq 3 3 1 :=
  ⟨by norm_num [cyclotomic_three], by decide⟩

-- Since 5 is 2 modulo 3, it divides no Φ₃(x) at a positive integer x.
example {x : ℤ} (hx : 0 < x) : ¬ (5 : ℤ) ∣ (cyclotomic 3 ℤ).eval x := fun h ↦
  (by decide : ¬ Nat.ModEq 3 5 1)
    (prime_modEq_one_of_dvd_cyclotomic_eval (by decide) (by decide) (by decide) hx h)

-- The criterion includes p = 2; Φ₂(3) is divisible by 2.
example : (2 : ℤ) ∣ (cyclotomic 2 ℤ).eval 3 :=
  ((prime_dvd_pow_self_sub_one_iff (p := 2) (x := 3) (by decide) (by decide)).mp
    (by decide)).2

-- A positive multiple of p is not congruent to 1 modulo p.
example : ¬ (3 : ℤ) ∣ (3 : ℤ) ^ 3 - 1 := by
  intro h
  have hx := ((prime_dvd_pow_self_sub_one_iff (p := 3) (x := 3) (by decide) (by decide)).mp h).1
  exact (by decide : ¬ (3 : ℤ) ∣ (3 : ℤ) - 1) hx

end MetaMathlibExt
