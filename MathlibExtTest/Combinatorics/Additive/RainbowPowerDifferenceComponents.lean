/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.RainbowPowerDifferenceComponents

open MetaMathlibExt

-- The boundary prime has no prime factors of p - 1 to check.
example : Nat.card (Quot fun a b : ZMod 2 => ∃ m n : ℕ, a ^ 2 ^ m = b ^ 2 ^ n) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  apply (card_powMap_components_eq_two_iff_of_even 2 2 ⟨1, rfl⟩ (by decide)).mpr
  intro q hq hdiv
  exact (hq.not_dvd_one hdiv).elim

-- Repeated factors are absorbed by iteration: 16 divides a power of 2, not 2 itself.
example : Nat.card (Quot fun a b : ZMod 17 => ∃ m n : ℕ, a ^ 2 ^ m = b ^ 2 ^ n) = 2 := by
  have : Fact (Nat.Prime 17) := ⟨by decide⟩
  apply (card_powMap_components_eq_two_iff_of_even 17 2 ⟨1, rfl⟩ (by decide)).mpr
  intro q hq hdiv
  exact hq.dvd_of_dvd_pow (n := 4) hdiv

-- The factor 3 of 7 - 1 does not divide the exponent 2.
example : Nat.card (Quot fun a b : ZMod 7 => ∃ m n : ℕ, a ^ 2 ^ m = b ^ 2 ^ n) ≠ 2 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  intro h
  exact (by decide : ¬ 3 ∣ 2)
    ((card_powMap_components_eq_two_iff_of_even 7 2 ⟨1, rfl⟩ (by decide)).mp h 3
      (by decide) (by decide))

-- The classification includes the prime 2, where there cannot be three components.
example : Nat.card (Quot fun a b : ZMod 2 => ∃ m n : ℕ, a ^ 3 ^ m = b ^ 3 ^ n) ≠ 3 := by
  have : Fact (Nat.Prime 2) := ⟨by decide⟩
  intro h
  obtain ⟨m, hm, _⟩ := (card_powMap_components_eq_three_iff_of_odd 2 3 ⟨1, rfl⟩ (by decide)).mp h
  omega

-- Here (19 - 1) / 2 = 9 divides an iterate exponent, even though it does not divide 3.
example : Nat.card (Quot fun a b : ZMod 19 => ∃ m n : ℕ, a ^ 3 ^ m = b ^ 3 ^ n) = 3 := by
  have : Fact (Nat.Prime 19) := ⟨by decide⟩
  apply (card_powMap_components_eq_three_iff_of_odd 19 3 ⟨1, rfl⟩ (by decide)).mpr
  refine ⟨9, rfl, fun q hq hdiv => ?_⟩
  exact hq.dvd_of_dvd_pow (n := 2) hdiv

-- Either 2 or an odd prime factor of (p - 1) / 2 can obstruct the criterion.
example : Nat.card (Quot fun a b : ZMod 5 => ∃ m n : ℕ, a ^ 3 ^ m = b ^ 3 ^ n) ≠ 3 := by
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro h
  obtain ⟨m, hm, hall⟩ :=
    (card_powMap_components_eq_three_iff_of_odd 5 3 ⟨1, rfl⟩ (by decide)).mp h
  have hm' : m = 2 := by omega
  exact (by decide : ¬ 2 ∣ 3) (hall 2 (by decide) (by simp [hm']))

example : Nat.card (Quot fun a b : ZMod 11 => ∃ m n : ℕ, a ^ 3 ^ m = b ^ 3 ^ n) ≠ 3 := by
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro h
  obtain ⟨m, hm, hall⟩ :=
    (card_powMap_components_eq_three_iff_of_odd 11 3 ⟨1, rfl⟩ (by decide)).mp h
  have hm' : m = 5 := by omega
  exact (by decide : ¬ 5 ∣ 3) (hall 5 (by decide) (by simp [hm']))
