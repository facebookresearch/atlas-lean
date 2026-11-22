/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.Muskingum

/-!
# Muskingum coefficient checks

Focused checks for `PhyslibExt.EarthScience.Muskingum`: at `K = 1`,
`X = 1 / 4`, `dt = 1` the coefficients are `(1 / 5, 3 / 5, 1 / 5)`, and
the admissibility window endpoints zero out `C2` and `C0` respectively.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Interior witness coefficients. -/
example : muskingumC0 1 (1 / 4) 1 = 1 / 5 ∧ muskingumC1 1 (1 / 4) 1 = 3 / 5
    ∧ muskingumC2 1 (1 / 4) 1 = 1 / 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [muskingumC0, muskingumC1, muskingumC2,
    muskingumDenominator]

/-- The admissibility characterization at the interior witness. -/
example : (0 ≤ muskingumC0 1 (1 / 4) 1 ∧ 0 ≤ muskingumC1 1 (1 / 4) 1
    ∧ 0 ≤ muskingumC2 1 (1 / 4) 1)
    ↔ 2 * (1 : ℝ) * (1 / 4) ≤ 1 ∧ 1 ≤ 2 * (1 : ℝ) * (1 - 1 / 4) :=
  muskingum_nonneg_iff (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- At the upper window endpoint `C2` vanishes; at the lower, `C0` does. -/
example : muskingumC2 1 (1 / 4) (3 / 2) = 0 ∧ muskingumC0 1 (1 / 4) (1 / 2) = 0 := by
  constructor <;> norm_num [muskingumC0, muskingumC2, muskingumDenominator]
