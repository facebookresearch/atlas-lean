/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.StrongPseudoprimeZPowNeg
import Mathlib.Data.ZMod.Basic

/-! # Tests for the closure of strong pseudoprime bases under powers and negation -/

namespace MetaMathlibExtTest

open MetaMathlibExt

-- Natural powers and inverses of a unit base, stated without integer exponents.
example {n : ℕ} {b : (ZMod n)ˣ} (h : IsStrongPseudoprime n (b : ZMod n)) (m : ℕ) :
    IsStrongPseudoprime n ((b : ZMod n) ^ m) := by
  simpa using (isStrongPseudoprime_zpow_and_neg h m).1

example {n : ℕ} {b : (ZMod n)ˣ} (h : IsStrongPseudoprime n (b : ZMod n)) :
    IsStrongPseudoprime n ((b⁻¹ : (ZMod n)ˣ) : ZMod n) := by
  simpa using (isStrongPseudoprime_zpow_and_neg h (-1)).1

-- Every odd composite is a strong pseudoprime to the base `-1`: here `n - 1 = 2 ^ k * d` with
-- `b ^ d = 1` for `b = 1`, and the negation step needs `0 < k`.
example {n : ℕ} (hn : 1 < n) (hcomp : ¬n.Prime) (hodd : Odd n) :
    IsStrongPseudoprime n (-1) := by
  have h1 : IsStrongPseudoprime n ((1 : (ZMod n)ˣ) : ZMod n) := by
    simpa using isStrongPseudoprime_one hn hcomp hodd
  simpa using (isStrongPseudoprime_zpow_and_neg h1 0).2

/-- The residue `2` as a unit modulo `2047 = 23 * 89`. -/
private def twoUnit : (ZMod 2047)ˣ :=
  ZMod.unitOfCoprime 2 (by decide)

private theorem coe_twoUnit : (twoUnit : ZMod 2047) = 2 := by
  simp [twoUnit]

private theorem isStrongPseudoprime_twoUnit : IsStrongPseudoprime 2047 (twoUnit : ZMod 2047) := by
  rw [coe_twoUnit]
  exact isStrongPseudoprime_2047_two

/-- `1024` is the inverse of `2` modulo `2047`. -/
private theorem twoUnit_mul : (twoUnit : ZMod 2047) * 1024 = 1 := by
  rw [coe_twoUnit]
  decide

-- Negation: `2047` is a strong pseudoprime to the base `-2 = 2045`. Here `2046 = 2 * 1023` and
-- `2 ^ 1023 = 1`, so the base `-2` passes through `(-2) ^ 1023 = -1` instead.
example : IsStrongPseudoprime 2047 2045 := by
  have h := (isStrongPseudoprime_zpow_and_neg isStrongPseudoprime_twoUnit 0).2
  rwa [coe_twoUnit, show (-2 : ZMod 2047) = 2045 by decide] at h

-- The exponent `t = 0` gives the base `1`.
example : IsStrongPseudoprime 2047 1 := by
  simpa using (isStrongPseudoprime_zpow_and_neg isStrongPseudoprime_twoUnit 0).1

-- The exponent `t = 2` gives the base `4`.
example : IsStrongPseudoprime 2047 4 := by
  have h := (isStrongPseudoprime_zpow_and_neg isStrongPseudoprime_twoUnit 2).1
  rwa [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, Units.val_pow_eq_pow_val, coe_twoUnit,
    show (2 : ZMod 2047) ^ 2 = 4 by decide] at h

-- The exponent `t = -1` gives the inverse `1024` of `2`.
example : IsStrongPseudoprime 2047 1024 := by
  have h := (isStrongPseudoprime_zpow_and_neg isStrongPseudoprime_twoUnit (-1)).1
  rwa [zpow_neg_one, Units.inv_eq_of_mul_eq_one_right twoUnit_mul] at h

-- A power followed by a negation: `-1024 = 1023`.
example : IsStrongPseudoprime 2047 1023 := by
  have h := (isStrongPseudoprime_zpow_and_neg
    (isStrongPseudoprime_zpow_and_neg isStrongPseudoprime_twoUnit (-1)).1 0).2
  rwa [zpow_neg_one, Units.inv_eq_of_mul_eq_one_right twoUnit_mul,
    show (-1024 : ZMod 2047) = 1023 by decide] at h

end MetaMathlibExtTest
