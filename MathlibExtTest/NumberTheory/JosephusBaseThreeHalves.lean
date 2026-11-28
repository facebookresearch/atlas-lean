/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.JosephusBaseThreeHalves

open MetaMathlibExt

example : baseThreeHalvesDigits 0 = [] := baseThreeHalvesDigits.eq_1

-- Multiples of three can have a zero least-significant digit.
example : baseThreeHalvesDigits 3 = [0, 1, 2] := by
  norm_num [baseThreeHalvesDigits.eq_1, baseThreeHalvesDigits.eq_2]

private theorem first_gap_zero : josephusThreeGap 0 = 0 := by
  simp only [josephusThreeGap, Nat.reduceAdd,
    josephusThreeFixedPoint_zero, josephusThreeFixedPoint_one]
  decide

-- The first two fixed points are adjacent, so their digit counts differ by one.
example : (baseThreeHalvesDigits 2).length = (baseThreeHalvesDigits 1).length + 1 := by
  simpa only [Nat.reduceAdd, josephusThreeFixedPoint_zero, josephusThreeFixedPoint_one,
    first_gap_zero, Nat.add_zero] using josephusThreeFixedPoint_digits_length 0

-- The three pure high extremal points between 2 and 13 account for four new digits.
example : (baseThreeHalvesDigits 13).length = (baseThreeHalvesDigits 2).length + 4 := by
  simpa only [Nat.reduceAdd, josephusThreeFixedPoint_one, josephusThreeFixedPoint_two,
    josephusThreeGap_one, Nat.add_assoc] using josephusThreeFixedPoint_digits_length 1

-- The first two fixed points are adjacent and the next digit is 1.
example : baseThreeHalvesDigits 2 = 1 :: baseThreeHalvesDigits 1 := by
  simpa only [Nat.reduceAdd, josephusThreeFixedPoint_zero, josephusThreeFixedPoint_one] using
    josephusThreeFixedPoint_digits_of_gap_zero 0 first_gap_zero

private theorem fixedPoint_three_eq_twenty : josephusThreeFixedPoint 3 = 20 := by
  have hp : 1 ≤ 20 ∧ josephus 3 20 = 20 := by decide
  have hc : Nat.count (fun n => 1 ≤ n ∧ josephus 3 n = n) 20 = 3 := by decide
  rw [← hc]
  exact Nat.nth_count hp

-- There are integers between 13 and 20, but none is pure high extremal.
example : baseThreeHalvesDigits 20 = 1 :: baseThreeHalvesDigits 13 := by
  have hgap : josephusThreeGap 2 = 0 := by
    simp only [josephusThreeGap, Nat.reduceAdd, josephusThreeFixedPoint_two,
      fixedPoint_three_eq_twenty]
    decide
  simpa only [Nat.reduceAdd, josephusThreeFixedPoint_two, fixedPoint_three_eq_twenty] using
    josephusThreeFixedPoint_digits_of_gap_zero 2 hgap

-- Between the fixed points 20 and 46, only 30 is pure high extremal.
example : baseThreeHalvesDigits 46 = [2, 0] ++ baseThreeHalvesDigits 20 := by
  have h46 : josephusThreeFixedPoint 4 = 46 := by
    have hp : 1 ≤ 46 ∧ josephus 3 46 = 46 := by decide +kernel
    have hc : Nat.count (fun n => 1 ≤ n ∧ josephus 3 n = n) 46 = 4 := by decide
    rw [← hc]
    exact Nat.nth_count hp
  have hgap : josephusThreeGap 3 = 1 := by
    simp only [josephusThreeGap, Nat.reduceAdd, fixedPoint_three_eq_twenty, h46]
    decide
  simpa only [Nat.reduceAdd, fixedPoint_three_eq_twenty, h46] using
    josephusThreeFixedPoint_digits_of_gap_one 3 hgap

-- The three pure high extremal points between `2` and `13` prepend the digits `2`, `1`, `1`, `0`.
example : baseThreeHalvesDigits 13 =
    2 :: List.replicate 2 1 ++ 0 :: baseThreeHalvesDigits 2 := by
  have hgap : 2 ≤ josephusThreeGap 1 := by
    have h3 := josephusThreeGap_one
    omega
  have h32 : (3 : ℕ) - 1 = 2 := rfl
  simpa only [Nat.reduceAdd, josephusThreeFixedPoint_one, josephusThreeFixedPoint_two,
    josephusThreeGap_one, h32] using
    josephusThreeFixedPoint_digits_of_gap_at_least_two 1 hgap

-- Hence the base-3/2 digits of `13` are `(2, 1, 1, 0, 1, 2)`, least significant first.
example : baseThreeHalvesDigits 13 = [2, 1, 1, 0, 1, 2] := by
  have h2 : baseThreeHalvesDigits 2 = [1, 2] := by
    norm_num [baseThreeHalvesDigits.eq_1, baseThreeHalvesDigits.eq_2]
  have hgap : 2 ≤ josephusThreeGap 1 := by
    have h3 := josephusThreeGap_one
    omega
  have h32 : (3 : ℕ) - 1 = 2 := rfl
  have h13 : baseThreeHalvesDigits 13 =
      2 :: List.replicate 2 1 ++ 0 :: baseThreeHalvesDigits 2 := by
    simpa only [Nat.reduceAdd, josephusThreeFixedPoint_one, josephusThreeFixedPoint_two,
      josephusThreeGap_one, h32] using
      josephusThreeFixedPoint_digits_of_gap_at_least_two 1 hgap
  rw [h13, h2]
  rfl
