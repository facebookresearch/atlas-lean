/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.Counting

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

example : Fintype.card {p : Partition 5 // 2 ≤ p.parts.count 1} = 3 := by
  rw [card_count_ge (by omega) (by omega)]
  exact card_three

example : Fintype.card {p : Partition 5 // 1 ≤ p.parts.count 2} = 3 := by
  rw [card_count_ge (by omega) (by omega)]
  exact card_three

example : Fintype.card {p : Partition 5 // 0 ≤ p.parts.count 2} = 7 := by
  rw [card_count_ge (by omega) (by omega)]
  exact card_five

example : Fintype.card {p : Partition 0 // 0 ≤ p.parts.count 1} = 1 := by
  rw [card_count_ge (by omega) (by omega)]
  exact card_zero

example :
    Fintype.card {p : Partition 1 // 1 ≤ p.parts.count 0} ≠
      Fintype.card (Partition (1 - 1 * 0)) := by
  have hempty : IsEmpty {p : Partition 1 // 1 ≤ p.parts.count 0} :=
    ⟨fun p => by
      have hm : 0 ∈ p.1.parts := Multiset.count_pos.mp (by omega)
      have hp := p.1.parts_pos hm
      omega⟩
  rw [Fintype.card_eq_zero_iff.mpr hempty, card_one]
  decide

example :
    Fintype.card {p : Partition 1 // 1 ≤ p.parts.count 2} ≠
      Fintype.card (Partition (1 - 1 * 2)) := by
  have hempty : IsEmpty {p : Partition 1 // 1 ≤ p.parts.count 2} :=
    ⟨fun p => by
      have hm : 2 ∈ p.1.parts := Multiset.count_pos.mp (by omega)
      have hle := p.1.le_of_mem_parts hm
      omega⟩
  rw [Fintype.card_eq_zero_iff.mpr hempty, card_zero]
  decide

example : Fintype.card (Partition 3) ≤ Fintype.card (Partition 5) := by
  exact card_monotone (by omega)

example : 3 * Fintype.card (Partition 3) = 9 := by
  rw [card_three]

example :
    (0 : ℕ) * Fintype.card (Partition 0) =
      ∑ v ∈ Icc 1 0, ∑ k ∈ Icc 1 (0 / v), v * Fintype.card (Partition (0 - k * v)) := by
  exact mul_card_eq_sum 0

example :
    (1 : ℕ) * Fintype.card (Partition 1) =
      ∑ v ∈ Icc 1 1, ∑ k ∈ Icc 1 (1 / v), v * Fintype.card (Partition (1 - k * v)) := by
  exact mul_card_eq_sum 1

#print axioms card_count_ge
#print axioms card_monotone
#print axioms mul_card_eq_sum

end Nat.Partition
