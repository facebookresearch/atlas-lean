/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.LinearLowerBound
import MathlibExt.Combinatorics.Enumerative.Partition.Counting

namespace Nat.Partition

open Finset

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

example : Fintype.card (Partition 0) = 1 := card_zero

example : Fintype.card (Partition 1) = 1 := card_one

example : Fintype.card (Partition 2) = 2 := card_two

example : Fintype.card (Partition 5) = 7 := card_five

example : 0 + 1 ≤ 2 * Fintype.card (Partition 0) := succ_le_two_mul_card 0

example : 1 + 1 ≤ 2 * Fintype.card (Partition 1) := succ_le_two_mul_card 1

example : 2 + 1 ≤ 2 * Fintype.card (Partition 2) := succ_le_two_mul_card 2

example : 5 + 1 ≤ 2 * Fintype.card (Partition 5) := succ_le_two_mul_card 5

example : 1 + 1 = 2 * Fintype.card (Partition 1) := by rw [card_one]

example (M : ℕ) : M ≤ Fintype.card (Partition (2 * M)) := by
  have h := succ_le_two_mul_card (2 * M)
  omega

example (lam : ℕ) : ∃ h : ℕ, 2 ≤ h ∧ 2 ^ lam ≤ Fintype.card (Partition h) := by
  refine ⟨2 ^ (lam + 1), ?_, ?_⟩
  · have := Nat.one_le_two_pow (n := lam)
    rw [pow_succ]
    omega
  · have h := succ_le_two_mul_card (2 ^ (lam + 1))
    have hp : 2 ^ (lam + 1) = 2 * 2 ^ lam := by rw [pow_succ']
    omega

example : ¬(1 + 1 ≤ Fintype.card (Partition 1)) := by
  rw [card_one]
  omega

#print axioms succ_le_two_mul_card

end Nat.Partition
