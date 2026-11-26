/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Recurrences.SylvesterSequence

open MathlibExt.NumberTheory.Recurrences.SylvesterSequenceWanted

example : sylvesterNumber 1 % 36 ≠ 7 := by decide

example : sylvesterNumber 2 = 7 := by decide

example (k : ℕ) : sylvesterNumber (k + 2) % 36 = 7 :=
  sylvester_modEq_seven_mod_thirty_six (k + 2) (by omega)

example : (36 : ℤ) ∣ (sylvesterNumber 3 : ℤ) - (sylvesterNumber 2 : ℤ) :=
  sylvester_sub_dvd (k := 2) (m := 2) (n := 3) (hk := by decide) (hm := by decide) (hn := by decide)

example : (36 : ℤ) ∣ (sylvesterNumber 2 : ℤ) - (sylvesterNumber 3 : ℤ) :=
  sylvester_sub_dvd 2 3 2 (by decide) (by decide) (by decide)

example : ¬ (36 : ℤ) ∣ (sylvesterNumber 2 : ℤ) - (sylvesterNumber 1 : ℤ) := by decide

example : sylvesterNumber 2 % 1764 ≠ 43 := by decide

example : sylvesterNumber 3 % 1764 = 43 := by decide

example : sylvesterNumber 4 % 1764 = 43 := by decide

example (k : ℕ) : sylvesterNumber (k + 3) % 1764 = 43 :=
  sylvester_modEq_forty_three_mod_1764 (k + 3) (by omega)

example : ∃ p : ℕ, p.Prime ∧ p ∣ sylvesterNumber 1 ∧ p % 4 = 3 :=
  sylvester_exists_prime_divisor_mod_four_eq_three 1 (by decide)

example : ¬ ∃ p : ℕ, p.Prime ∧ p ∣ sylvesterNumber 0 ∧ p % 4 = 3 := by
  rintro ⟨p, -, hpdvd, hpmod⟩
  have hle : p ≤ 2 := Nat.le_of_dvd (by decide : 0 < sylvesterNumber 0) hpdvd
  omega

example : Nat.Prime 139 ∧ 139 ∣ sylvesterNumber 4 ∧ 139 % 4 = 3 := by decide
