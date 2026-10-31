/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.LogBounds

import MathlibExt.Combinatorics.Enumerative.Partition.Counting

namespace Nat.Partition

open Finset

private def p (n : ℕ) : ℕ := Fintype.card (Partition n)

private noncomputable def cHR : ℝ := Real.pi * Real.sqrt ((2 : ℝ) / 3)

private noncomputable def kappa : ℝ := cHR / Real.log 2

private def Bounds (B C : ℝ) : Prop :=
  (∀ n : ℕ, 1 ≤ n → kappa * Real.sqrt n - B * Real.logb 2 n - C ≤ Real.logb 2 (p n)) ∧
    ∀ n : ℕ, Real.logb 2 (p n) ≤ kappa * Real.sqrt n + C

private lemma card_zero : Fintype.card (Partition 0) = 1 := Fintype.card_unique

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
    ∃ B C : ℝ,
      (∀ n : ℕ, 1 ≤ n →
        (Real.pi * Real.sqrt ((2 : ℝ) / 3) / Real.log 2) * Real.sqrt n -
              B * Real.logb 2 (n : ℝ) - C ≤
            Real.logb 2 (Fintype.card (Partition n) : ℝ)) ∧
      (∀ n : ℕ,
        Real.logb 2 (Fintype.card (Partition n) : ℝ) ≤
          (Real.pi * Real.sqrt ((2 : ℝ) / 3) / Real.log 2) * Real.sqrt n + C) :=
  exists_logb_card_bounds

example : ∃ B C : ℝ, Bounds B C := by
  simpa only [Bounds, kappa, cHR, p] using exists_logb_card_bounds

example : ∃ B C : ℝ,
    (Real.pi * Real.sqrt ((2 : ℝ) / 3) / Real.log 2) * Real.sqrt 1 -
          B * Real.logb 2 (1 : ℝ) - C ≤ Real.logb 2 (1 : ℝ) ∧
    (Real.pi * Real.sqrt ((2 : ℝ) / 3) / Real.log 2) * Real.sqrt 5 -
          B * Real.logb 2 (5 : ℝ) - C ≤ Real.logb 2 (7 : ℝ) ∧
    Real.logb 2 (1 : ℝ) ≤
      (Real.pi * Real.sqrt ((2 : ℝ) / 3) / Real.log 2) * Real.sqrt 0 + C := by
  obtain ⟨B, C, hlow, hupp⟩ := exists_logb_card_bounds
  exact ⟨B, C,
    by simpa [card_one] using hlow 1 (by omega),
    by simpa [card_five] using hlow 5 (by omega),
    by simpa [card_zero] using hupp 0⟩

example : ¬ ∀ n : ℕ, 1 ≤ n →
    (Real.pi * Real.sqrt ((2 : ℝ) / 3) / Real.log 2) * Real.sqrt n -
          (0 : ℝ) * Real.logb 2 (n : ℝ) - 0 ≤
        Real.logb 2 (Fintype.card (Partition n) : ℝ) := by
  intro h
  have hle := h 1 (by omega)
  rw [card_one, Nat.cast_one] at hle
  have hpos : 0 < Real.pi * Real.sqrt ((2 : ℝ) / 3) / Real.log 2 := by positivity
  simp only [Real.sqrt_one, mul_one, zero_mul, sub_zero, Real.logb, Real.log_one,
    zero_div] at hle
  linarith

#print axioms exists_logb_card_bounds

end Nat.Partition
