/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.ExponentialUpperBound

import MathlibExt.Combinatorics.Enumerative.Partition.Counting

namespace Nat.Partition

open Finset

private abbrev p (n : ℕ) := Fintype.card (Partition n)

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

example (n : ℕ) :
    (Fintype.card (Partition n) : ℝ) ≤
      Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt n) :=
  card_le_exp n

example (n : ℕ) :
    (p n : ℝ) ≤ Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt n) :=
  card_le_exp n

example : (1 : ℝ) ≤ Real.exp 0 := by
  convert card_le_exp 0 using 1 <;> norm_num

example : (1 : ℝ) ≤ Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3)) := by
  simpa [card_one] using card_le_exp 1

example : (3 : ℝ) ≤
    Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt 3) := by
  simpa [card_three] using card_le_exp 3

example : (7 : ℝ) ≤
    Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt 5) := by
  simpa [card_five] using card_le_exp 5

example {E v k : ℕ} (hv : 1 ≤ v) (hkv : k * v ≤ E) :
    (Fintype.card {p : Partition E // k ≤ p.parts.count v} : ℝ) ≤
      Real.exp (Real.pi * Real.sqrt ((2 : ℝ) / 3) * Real.sqrt (E - k * v)) := by
  rw [card_count_ge hv hkv]
  simpa only [Nat.cast_sub hkv, Nat.cast_mul] using card_le_exp (E - k * v)

#print axioms card_le_exp

end Nat.Partition
