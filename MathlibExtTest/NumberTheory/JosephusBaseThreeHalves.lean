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
