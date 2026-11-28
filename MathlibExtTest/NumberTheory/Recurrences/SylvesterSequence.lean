/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Data.Set.Insert
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

-- The two witnesses are the index of 3 and the triangular index of 3.
example : 3 ∈ {x : ℕ | ∃ n m : ℕ, 1 ≤ m ∧ x = sylvesterNumber n ∧
    2 * x = m * (m + 1)} :=
  ⟨1, 2, by decide, by decide, by decide⟩

-- Independently exclude 2, 7, and 43 by bounding their doubles between consecutive products.
example : (¬ ∃ m : ℕ, 1 ≤ m ∧ 2 * sylvesterNumber 0 = m * (m + 1)) ∧
    (¬ ∃ m : ℕ, 1 ≤ m ∧ 2 * sylvesterNumber 2 = m * (m + 1)) ∧
    (¬ ∃ m : ℕ, 1 ≤ m ∧ 2 * sylvesterNumber 3 = m * (m + 1)) := by
  have gap (n k : ℕ) (hl : k * (k + 1) < 2 * sylvesterNumber n)
      (hu : 2 * sylvesterNumber n < (k + 1) * (k + 2)) :
      ¬ ∃ m : ℕ, 1 ≤ m ∧ 2 * sylvesterNumber n = m * (m + 1) := by
    rintro ⟨m, -, hm⟩
    rw [hm] at hl hu
    rcases le_or_gt m k with h | h
    · exact (not_lt_of_ge (Nat.mul_le_mul h (Nat.add_le_add_right h 1))) hl
    · have h₁ : k + 1 ≤ m := h
      have h₂ : k + 2 ≤ m + 1 := Nat.add_le_add_right h₁ 1
      exact (not_lt_of_ge (Nat.mul_le_mul h₁ h₂)) hu
  exact ⟨gap 0 1 (by decide) (by decide), gap 2 3 (by decide) (by decide),
    gap 3 8 (by decide) (by decide)⟩

-- A client can rewrite triangular Sylvester membership to singleton membership.
example : sylvesterNumber 4 ∉ {x : ℕ | ∃ n m : ℕ, 1 ≤ m ∧ x = sylvesterNumber n ∧
    2 * x = m * (m + 1)} := by
  rw [triangular_sylvester_values_eq]
  decide
