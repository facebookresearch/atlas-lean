/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ShiftedFloorThresholdCounts
import Mathlib.Tactic.NormNum

open MetaMathlibExt

-- The empty interval contributes at neither threshold, even when the shift is nonzero.
example : ((Finset.Icc 1 0).filter (fun d : ℕ => (1 : ℤ) ≤ ⌊(0 : ℝ) / d + 1 / 2⌋)).card = 0 := by
  simpa only [Nat.cast_zero, sub_zero] using
    (shifted_floor_sequence_card_ge 0 (1 / 2) 0
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

example : ((Finset.Icc 1 0).filter (fun d : ℕ => (2 : ℤ) ≤ ⌊(0 : ℝ) / d + 1 / 2⌋)).card = 0 := by
  have h := (shifted_floor_sequence_card_ge 0 (1 / 2) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2 2 (by decide)
  simpa only [Nat.cast_zero, Nat.cast_ofNat, sub_zero, zero_div, Int.floor_zero,
    Int.natCast_eq_zero] using h

-- At `ν = n * α`, the last denominator still meets the first threshold.
example : ((Finset.Icc 1 3).filter
    (fun d : ℕ => (1 : ℤ) ≤ ⌊((3 : ℝ) - 3 / 4) / d + 1 / 4⌋)).card = 3 :=
  (shifted_floor_sequence_card_ge 3 (1 / 4) (3 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

-- At threshold 2 the real cutoff is `19 / 6`, so exactly three terms qualify.
example : (((Finset.Icc 1 5).filter
    (fun d : ℕ => (2 : ℤ) ≤ ⌊((5 : ℝ) - 1 / 4) / d + 1 / 2⌋)).card : ℤ) = 3 := by
  refine ((shifted_floor_sequence_card_ge 5 (1 / 2) (1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2 2 (by decide)).trans ?_
  exact Int.floor_eq_iff.mpr (by norm_num)

-- An integral cutoff includes the endpoint (the term at `d = 2` reaches 2 exactly).
example : (((Finset.Icc 1 3).filter
    (fun d : ℕ => ((2 : ℕ) : ℤ) ≤ ⌊((3 : ℕ) : ℝ) / d + 1 / 2⌋)).card : ℤ) = 2 := by
  have h := (shifted_floor_sequence_card_ge 3 (1 / 2) 0
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2 2 (by decide)
  have hfloor : ⌊((3 : ℝ) - 0) / ((2 : ℕ) - (1 / 2 : ℝ))⌋ = (2 : ℤ) :=
    Int.floor_eq_iff.mpr (by norm_num)
  simpa only [sub_zero] using h.trans hfloor
