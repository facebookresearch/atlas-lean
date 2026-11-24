/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Digits.OrdinaryMomentRecurrence
import Mathlib.Tactic.NormNum

open MetaMathlibExt Filter

example : digitPowerSum 2 1 0 = 1 := by
  norm_num [digitPowerSum, Finset.sum_range_succ]

example (m : ℕ) (hm : 0 < m) : digitPowerSum 2 1 m = 0 := by
  norm_num [digitPowerSum, Finset.sum_range_succ, hm.ne']

-- In the exceptional binary row every positive moment vanishes. The next row already has
-- first moment 2/3, and the first moments converge to 1.
example (u : ℕ → ℕ → ℝ) (hu : OrdinaryMomentRecurrence 2 1 u) :
    (∀ m, 1 ≤ m → u 0 m = 0) ∧ u 1 1 = 2 / 3 ∧
      Tendsto (fun j => u j 1) atTop (nhds 1) := by
  obtain ⟨h0, hz, _, _, hlim⟩ := ordinaryMomentRecurrence_properties 2 1 (by decide)
    (by decide) u hu
  have hzero (m : ℕ) (hm : 1 ≤ m) := (hz 0 m hm).2.mpr ⟨rfl, rfl, rfl⟩
  refine ⟨hzero, ?_, ?_⟩
  · have he := hu.2.2 1 le_rfl 1
    norm_num [digitPowerSum, Finset.sum_range_succ, hzero 1 le_rfl, h0] at he
    linarith
  · convert hlim 1 le_rfl using 2
    norm_num
