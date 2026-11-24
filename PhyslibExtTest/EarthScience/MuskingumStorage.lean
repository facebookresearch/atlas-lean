/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.MuskingumStorage

/-!
# Muskingum storage checks

Focused checks for `PhyslibExt.EarthScience.MuskingumStorage`:
a constant inflow/outflow state satisfies both sides of the
balance correspondence, and a routed pulse step with inputs in
`[10, 100]` stays in that interval.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Constant state: recurrence and balance both hold. -/
example : muskingumStorage 1 (1 / 4) 10 10
      - muskingumStorage 1 (1 / 4) 10 10
    = 1 * ((10 + 10) - (10 + 10)) / 2
  ∧ (10 : ℝ) = muskingumC0 1 (1 / 4) 1 * 10
      + muskingumC1 1 (1 / 4) 1 * 10 + muskingumC2 1 (1 / 4) 1 * 10 := by
  constructor
  · norm_num [muskingumStorage]
  · have h := (muskingum_storage_balance_iff (K := 1) (X := 1 / 4)
      (dt := 1) (I0 := 10) (I1 := 10) (O0 := 10) (O1 := 10)
      (by norm_num [muskingumDenominator])).mpr
    exact h (by norm_num [muskingumStorage])

/-- Pulse step: inputs in `[10, 100]` keep the outflow there. -/
example : muskingumC0 1 (1 / 4) 1 * 100 + muskingumC1 1 (1 / 4) 1 * 10
      + muskingumC2 1 (1 / 4) 1 * 10 ∈ Set.Icc 10 100 :=
  muskingum_outflow_mem_Icc (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩ ⟨by norm_num, by norm_num⟩
    ⟨by norm_num, by norm_num⟩
