/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.CarbonateSpeciation

/-!
# Carbonate speciation and alkalinity checks

Concrete consumers of `PhyslibExt.EarthScience.CarbonateSpeciation`:
mass closure at `C0 = K1 = K2 = Kw = 1, h = 1`, the boundary `C0 = 0`,
strict decrease of alkalinity, and the unique root at `A0 = 1`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. At the
witness parameters the three species are `1/3` each, alkalinity is `1`,
and `h = 1` is the unique root of `A(h) = 1`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Mass closure, witness and boundary
- B. Monotonicity and the unique root
-/

/-- Mass closure at the witness parameters: the three species sum to `1`. -/
example : (1 : ℝ) * (1 : ℝ) ^ 2 / ((1 : ℝ) ^ 2 + 1 * 1 + 1 * 1) +
    (1 : ℝ) * 1 * 1 / ((1 : ℝ) ^ 2 + 1 * 1 + 1 * 1) +
    (1 : ℝ) * 1 * 1 / ((1 : ℝ) ^ 2 + 1 * 1 + 1 * 1) = 1 :=
  EarthScience.carbonate_species_sum 1 1 1 1 (by norm_num) (by norm_num)
    (by norm_num)

/-- Boundary `C0 = 0`: no dissolved inorganic carbon, all species zero. -/
example : (0 : ℝ) * (1 : ℝ) ^ 2 / ((1 : ℝ) ^ 2 + 1 * 1 + 1 * 1) +
    (0 : ℝ) * 1 * 1 / ((1 : ℝ) ^ 2 + 1 * 1 + 1 * 1) +
    (0 : ℝ) * 1 * 1 / ((1 : ℝ) ^ 2 + 1 * 1 + 1 * 1) = 0 :=
  EarthScience.carbonate_species_sum 0 1 1 1 (by norm_num) (by norm_num)
    (by norm_num)

/-- Alkalinity strictly decreases: `A(2) < A(1)` at the witness parameters. -/
example : (1 : ℝ) * (1 * 2 + 2 * 1 * 1) / (2 ^ 2 + 1 * 2 + 1 * 1) + 1 / 2 - 2 <
    (1 : ℝ) * (1 * 1 + 2 * 1 * 1) / (1 ^ 2 + 1 * 1 + 1 * 1) + 1 / 1 - 1 := by
  have h := EarthScience.alkalinity_strictAntiOn 1 1 1 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  exact h (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 1))
    (Set.mem_Ioi.mpr (by norm_num : (0 : ℝ) < 2)) (by norm_num)

/-- At the witness parameters, `h = 1` is the unique root of `A(h) = 1`. -/
example : ∃! h, 0 < h ∧
    (1 : ℝ) * (1 * h + 2 * 1 * 1) / (h ^ 2 + 1 * h + 1 * 1) + 1 / h - h = 1 :=
  EarthScience.alkalinity_unique_root 1 1 1 1 1 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
