/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Tactic.NormNum
import MathlibExt.NumberTheory.JosephusBaseThreeHalvesJosephusThreeFixedPointDigitsOfGapAtLeastTwo

open MetaMathlibExt

namespace MathlibExtTest.NumberTheory.JosephusBaseThreeHalvesJosephusThreeFixedPointDigitsOfGapAtLeastTwo

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

end MathlibExtTest.NumberTheory.JosephusBaseThreeHalvesJosephusThreeFixedPointDigitsOfGapAtLeastTwo
