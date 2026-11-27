/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.StrongPseudoprimePrimitivePartPowers

open MetaMathlibExt Polynomial

-- The minus case, taking the inverse of the residue of 16 modulo 91.
example : IsStrongPseudoprime 91
    (((ZMod.unitOfCoprime 16 (by decide : Nat.Coprime 16 91)) ^ (-1 : ℤ) : (ZMod 91)ˣ) : ZMod 91) := by
  have hcomp : ¬Nat.Prime 91 := Nat.not_prime_mul (a := 7) (b := 13) (by decide) (by decide)
  refine isStrongPseudoprime_zpow_of_dvd_primitivePart (b := 16) (m := 3)
    (by decide) (by decide) (by decide) hcomp (Or.inl ?_) _ (by simp) (-1)
  have heval : (cyclotomic 3 ℤ).eval 16 = 273 := by
    norm_num [cyclotomic_three, eval_add, eval_pow, eval_X, eval_one]
  change (91 : ℤ) ∣ (cyclotomic 3 ℤ).eval 16 / (Int.gcd ((cyclotomic 3 ℤ).eval 16) 3 : ℤ)
  rw [heval]
  decide

-- The plus case, where the zero exponent gives base one.
example : IsStrongPseudoprime 91 1 := by
  let u : (ZMod 91)ˣ := ZMod.unitOfCoprime 17 (by decide : Nat.Coprime 17 91)
  have hcomp : ¬Nat.Prime 91 := Nat.not_prime_mul (a := 7) (b := 13) (by decide) (by decide)
  have hd : (91 : ℤ) ∣ (cyclotomic 6 ℤ).eval 17 / (Int.gcd ((cyclotomic 6 ℤ).eval 17) 3 : ℤ) := by
    have heval : (cyclotomic 6 ℤ).eval 17 = 273 := by
      norm_num [cyclotomic_six, eval_add, eval_sub, eval_pow, eval_X, eval_one]
    rw [heval]
    decide
  simpa using isStrongPseudoprime_zpow_of_dvd_primitivePart (b := 17) (m := 3)
    (by decide) (by decide) (by decide) hcomp (Or.inr hd) u (by simp [u]) 0
