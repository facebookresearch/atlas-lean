/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FermatNumberStrongPseudoprimeTwoPow
import Mathlib.Data.ZMod.Basic

/-! # Tests for strong pseudoprime bases of composite Fermat numbers -/

namespace MetaMathlibExtTest

open MetaMathlibExt

/-- The residue `2` as a unit modulo a Fermat number, which is odd. -/
private def twoUnit (k : ℕ) : (ZMod (Nat.fermatNumber k))ˣ :=
  ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr (Nat.odd_fermatNumber k))

private theorem coe_twoUnit (k : ℕ) : (twoUnit k : ZMod (Nat.fermatNumber k)) = 2 := by
  simp [twoUnit]

/-- `F_5 = 2 ^ 32 + 1 = 641 * 6700417` is composite, so the hypothesis is satisfiable. -/
private theorem fermatNumber_five_not_prime : ¬(Nat.fermatNumber 5).Prime := by
  rw [show Nat.fermatNumber 5 = 641 * 6700417 by norm_num [Nat.fermatNumber]]
  exact Nat.not_prime_mul (by norm_num) (by norm_num)

-- With `t = 1`: every composite Fermat number is a strong pseudoprime to the base `2`.
example {k : ℕ} (hk : ¬(Nat.fermatNumber k).Prime) :
    IsStrongPseudoprime (Nat.fermatNumber k) 2 := by
  simpa [coe_twoUnit] using
    fermatNumber_isStrongPseudoprime_two_zpow hk (twoUnit k) (coe_twoUnit k) 1

example : IsStrongPseudoprime (Nat.fermatNumber 5) 2 := by
  simpa [coe_twoUnit] using
    fermatNumber_isStrongPseudoprime_two_zpow fermatNumber_five_not_prime (twoUnit 5)
      (coe_twoUnit 5) 1

-- With `t = -1`: `F_5` is a strong pseudoprime to the inverse `(F_5 + 1) / 2 = 2147483649` of `2`.
example : IsStrongPseudoprime (Nat.fermatNumber 5) 2147483649 := by
  have h := fermatNumber_isStrongPseudoprime_two_zpow fermatNumber_five_not_prime (twoUnit 5)
    (coe_twoUnit 5) (-1)
  have hinv : (twoUnit 5 : ZMod (Nat.fermatNumber 5)) * 2147483649 = 1 := by
    rw [coe_twoUnit]; decide
  rwa [zpow_neg_one, Units.inv_eq_of_mul_eq_one_right hinv] at h

-- With `t = 2 ^ 5`: the base `2 ^ 32` is `-1` modulo `F_5`.
example : IsStrongPseudoprime (Nat.fermatNumber 5) (-1) := by
  have h := fermatNumber_isStrongPseudoprime_two_zpow fermatNumber_five_not_prime (twoUnit 5)
    (coe_twoUnit 5) (2 ^ 5)
  have h32 : (2 : ZMod (Nat.fermatNumber 5)) ^ 32 = -1 := by decide
  rwa [show ((2 : ℤ) ^ 5) = ((32 : ℕ) : ℤ) by norm_num, zpow_natCast, Units.val_pow_eq_pow_val,
    coe_twoUnit, h32] at h

end MetaMathlibExtTest
