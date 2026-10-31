/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.ExponentialLowerBound

namespace Nat.Partition

open Finset

private abbrev p (n : ℕ) : ℝ := Fintype.card (Partition n)

private lemma card_one : Fintype.card (Partition 1) = 1 := Fintype.card_unique

private lemma Icc_one_two : Icc 1 2 = {1, 2} := by decide

private lemma Icc_one_three : Icc 1 3 = {1, 2, 3} := by decide

private lemma Icc_one_four : Icc 1 4 = {1, 2, 3, 4} := by decide

private lemma Icc_one_five : Icc 1 5 = {1, 2, 3, 4, 5} := by decide

private lemma card_two : Fintype.card (Partition 2) = 2 := by
  have h := mul_card_eq_sum 2
  simp [Icc_one_two] at h
  omega

private lemma card_three : Fintype.card (Partition 3) = 3 := by
  have h := mul_card_eq_sum 3
  simp [Icc_one_three, card_two] at h
  omega

private lemma card_four : Fintype.card (Partition 4) = 5 := by
  have h := mul_card_eq_sum 4
  simp [Icc_one_two, Icc_one_four, card_two, card_three] at h
  omega

private lemma card_five : Fintype.card (Partition 5) = 7 := by
  have h := mul_card_eq_sum 5
  simp [Icc_one_two, Icc_one_five, card_two, card_three, card_four] at h
  omega

example :
    ∃ (H : ℝ) (B : ℕ), 0 < H ∧ ∀ n : ℕ, 1 ≤ n →
      H * Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt n) / (n : ℝ) ^ B ≤
        (Fintype.card (Partition n) : ℝ) :=
  exists_exp_div_pow_le_card

example : ∃ (H : ℝ) (B : ℕ), 0 < H ∧ ∀ n : ℕ, 1 ≤ n →
    H * Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt n) / (n : ℝ) ^ B ≤
      p n := by
  simpa only using exists_exp_div_pow_le_card

example : ∃ (H : ℝ) (B : ℕ), 0 < H ∧
    H * Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt 1) / (1 : ℝ) ^ B ≤ 1 := by
  obtain ⟨H, B, hH, h⟩ := exists_exp_div_pow_le_card
  exact ⟨H, B, hH, by simpa [card_one] using h 1 (by omega)⟩

example : ∃ (H : ℝ) (B : ℕ), 0 < H ∧
    H * Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt 5) / (5 : ℝ) ^ B ≤ 7 := by
  obtain ⟨H, B, hH, h⟩ := exists_exp_div_pow_le_card
  exact ⟨H, B, hH, by simpa [card_five] using h 5 (by omega)⟩

example : ¬ ∀ n : ℕ, 1 ≤ n →
    Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt n) ≤
      (Fintype.card (Partition n) : ℝ) := by
  intro h
  have hle := h 1 (by omega)
  rw [card_one, Nat.cast_one] at hle
  have hpos : 0 < Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt 1 := by positivity
  exact (not_lt_of_ge hle) (Real.one_lt_exp_iff.mpr hpos)

#print axioms exists_exp_div_pow_le_card

end Nat.Partition
