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

-- The first two fixed points are adjacent, so their digit counts differ by one.
example : (baseThreeHalvesDigits 2).length = (baseThreeHalvesDigits 1).length + 1 := by
  have hgap : josephusThreeGap 0 = 0 := by
    simp only [josephusThreeGap, Nat.reduceAdd,
      josephusThreeFixedPoint_zero, josephusThreeFixedPoint_one]
    decide
  simpa only [Nat.reduceAdd, josephusThreeFixedPoint_zero, josephusThreeFixedPoint_one, hgap,
    Nat.add_zero] using josephusThreeFixedPoint_digits_length 0

-- The three pure high extremal points between 2 and 13 account for four new digits.
example : (baseThreeHalvesDigits 13).length = (baseThreeHalvesDigits 2).length + 4 := by
  simpa only [Nat.reduceAdd, josephusThreeFixedPoint_one, josephusThreeFixedPoint_two,
    josephusThreeGap_one, Nat.add_assoc] using josephusThreeFixedPoint_digits_length 1

-- Between the fixed points 20 and 46, only 30 is pure high extremal.
example : baseThreeHalvesDigits 46 = [2, 0] ++ baseThreeHalvesDigits 20 := by
  have h20 : josephusThreeFixedPoint 3 = 20 := by
    have hp : 1 ≤ 20 ∧ josephus 3 20 = 20 := by decide
    have hc : Nat.count (fun n => 1 ≤ n ∧ josephus 3 n = n) 20 = 3 := by decide
    rw [← hc]
    exact Nat.nth_count hp
  have h46 : josephusThreeFixedPoint 4 = 46 := by
    have hp : 1 ≤ 46 ∧ josephus 3 46 = 46 := by decide +kernel
    have hc : Nat.count (fun n => 1 ≤ n ∧ josephus 3 n = n) 46 = 4 := by decide
    rw [← hc]
    exact Nat.nth_count hp
  have hgap : josephusThreeGap 3 = 1 := by
    simp only [josephusThreeGap, Nat.reduceAdd, h20, h46]
    decide
  simpa only [Nat.reduceAdd, h20, h46] using josephusThreeFixedPoint_digits_of_gap_one 3 hgap
