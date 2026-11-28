/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RoughNumberSieve
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Boundary cases for the rough-number sieve

At the upper bound `28.5`, increasing the threshold from `4.5` to `5` removes both `5` and
`25`. The next prime, `29`, lies outside both counts.
-/

open Finset

example : ∃ C : ℝ, 8 ≤ C * (57 / 2) / Real.log (9 / 2) ∧
    6 ≤ C * (57 / 2) / Real.log 5 := by
  obtain ⟨C, hC⟩ := MetaMathlibExt.card_minFac_gt_le_div_log
  have at_cutoff (y : ℝ) (hy : 2 ≤ y) (hy' : y ≤ 57 / 2) :
      (((Icc 1 28).filter (fun n => ⌊y⌋₊ < Nat.minFac n)).card : ℝ) ≤
        C * (57 / 2) / Real.log y := by
    have h := hC (57 / 2) y hy hy'
    simpa only [show ⌊(57 / 2 : ℝ)⌋₊ = 28 by norm_num,
      ← Nat.floor_lt (show 0 ≤ y by linarith)] using h
  refine ⟨C, ?_, ?_⟩
  · have h := at_cutoff (9 / 2) (by norm_num) (by norm_num)
    simpa only [show ⌊(9 / 2 : ℝ)⌋₊ = 4 by norm_num,
      show ((Icc 1 28).filter (fun n => 4 < Nat.minFac n)).card = 8 by decide +kernel,
      Nat.cast_ofNat]
      using h
  · have h := at_cutoff 5 (by norm_num) (by norm_num)
    simpa only [show ⌊(5 : ℝ)⌋₊ = 5 by norm_num,
      show ((Icc 1 28).filter (fun n => 5 < Nat.minFac n)).card = 6 by decide +kernel,
      Nat.cast_ofNat]
      using h
