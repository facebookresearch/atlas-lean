/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.WieferichOrder
import MathlibExt.NumberTheory.WieferichPrime
import Mathlib.Tactic.NormNum.Prime

/-! # Tests for `MathlibExt.NumberTheory.WieferichOrder` -/

namespace MathlibExtTest.WieferichOrder

open MetaMathlibExt

-- `11` is a Wieferich prime to base `3` (`3 ^ 5 = 243 = 2 * 121 + 1`), so the order of `3`
-- modulo `11 ^ 2` is its order `5` modulo `11`.
example : orderOf (3 : ZMod (11 ^ 2)) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h11 : orderOf (3 : ZMod 11) = 5 := orderOf_eq_prime (by decide) (by decide)
  have h := (pow_sub_one_modEq_one_sq_iff_orderOf_eq (a := 3) (p := 11) (by norm_num)
    (by norm_num)).mp (by decide)
  simpa [h11] using h

-- `5` is not a Wieferich prime to base `2` (`2 ^ 4 = 16`), so the orders of `2` modulo `5 ^ 2`
-- and modulo `5` differ.
example : orderOf (2 : ZMod (5 ^ 2)) ≠ orderOf (2 : ZMod 5) := by
  intro h
  have h' := (pow_sub_one_modEq_one_sq_iff_orderOf_eq (a := 2) (p := 5) (by norm_num)
    (by norm_num)).mpr (by simpa using h)
  revert h'
  decide

-- The prime `2` is allowed: `3 ≢ 1 [MOD 4]`, so the orders of `3` modulo `2 ^ 2` and modulo `2`
-- differ.
example : orderOf (3 : ZMod (2 ^ 2)) ≠ orderOf (3 : ZMod 2) := by
  intro h
  have h' := (pow_sub_one_modEq_one_sq_iff_orderOf_eq (a := 3) (p := 2) Nat.prime_two
    (by norm_num)).mpr (by simpa using h)
  revert h'
  decide

-- The Wieferich prime `1093` to base `2`: the order of `2` is the same modulo `1093 ^ 2` and
-- modulo `1093`.
example : orderOf (2 : ZMod (1093 ^ 2)) = orderOf (2 : ZMod 1093) := by
  simpa using (pow_sub_one_modEq_one_sq_iff_orderOf_eq (a := 2) (p := 1093) (by norm_num)
    (by norm_num)).mp (by decide +kernel)

-- For an odd prime `p`, `Nat.IsWieferichPrime p` (base two) says that the order of `2` is the
-- same modulo `p ^ 2` and modulo `p`.
example {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p.IsWieferichPrime ↔ orderOf (2 : ZMod (p ^ 2)) = orderOf (2 : ZMod p) := by
  rw [Nat.isWieferichPrime_iff_modEq, and_iff_right hp]
  simpa using pow_sub_one_modEq_one_sq_iff_orderOf_eq (a := 2) hp
    fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

-- The hypothesis `¬ p ∣ a` cannot be dropped: for `a = p = 3` both orders are `0`, since `3` is
-- a unit neither modulo `3 ^ 2` nor modulo `3`, while `3 ^ 2 ≢ 1 [MOD 3 ^ 2]`.
example : orderOf ((3 : ℕ) : ZMod (3 ^ 2)) = orderOf ((3 : ℕ) : ZMod 3) ∧
    ¬ 3 ^ (3 - 1) ≡ 1 [MOD 3 ^ 2] := by
  have h9 : orderOf ((3 : ℕ) : ZMod (3 ^ 2)) = 0 := orderOf_eq_zero_iff.mpr fun h =>
    absurd ((ZMod.isUnit_iff_coprime 3 (3 ^ 2)).mp h.isUnit) (by decide)
  have h3 : orderOf ((3 : ℕ) : ZMod 3) = 0 := orderOf_eq_zero_iff.mpr fun h =>
    absurd ((ZMod.isUnit_iff_coprime 3 3).mp h.isUnit) (by decide)
  exact ⟨h9.trans h3.symm, by decide⟩

end MathlibExtTest.WieferichOrder
