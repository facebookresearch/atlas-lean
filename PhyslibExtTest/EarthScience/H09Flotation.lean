/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.H09Flotation

/-!
# Flotation checks

Concrete consumers of `PhyslibExt.EarthScience.H09Flotation`:
ice `ρi = 917`, water `ρw = 1028`, thickness `H = 100` (submerged depth
`89.20…`, fraction `917 / 1028`), plus the equal-density boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric flotation
- B. Equal-density boundary

## iv. References

- `PhyslibExt.EarthScience.H09Flotation`
-/

/-- Numeric flotation: `ρi = 917`, `ρw = 1028`, `H = 100`, balance
`1028 * d = 917 * 100` gives `d = 917 / 1028 * 100`, `0 < d < 100`. -/
example (d : ℝ) (hbal : 1028 * d = 917 * 100) :
    d = 917 / 1028 * 100 ∧ 0 < d ∧ d < 100 ∧ d / 100 = 917 / 1028 :=
  EarthScience.flotation_submerged_fraction (ρi := 917) (ρw := 1028) (H := 100)
    (by norm_num) (by norm_num) (by norm_num) hbal

/-- Numeric flotation: submerged fraction is below 1, via the theorem. -/
example : (917 : ℝ) / 1028 < 1 := by
  have h := EarthScience.flotation_submerged_fraction (ρi := 917) (ρw := 1028)
    (H := 100) (d := 917 / 1028 * 100) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  rw [← h.2.2.2, div_lt_one (by norm_num : (0 : ℝ) < 100)]
  exact h.2.2.1

/-- Equal-density boundary: `ρ = 1000` gives `d = H`. -/
example (d : ℝ) (hbal : 1000 * d = 1000 * 100) : d = 100 :=
  EarthScience.flotation_equal_density (ρ := 1000) (H := 100) (by norm_num)
    (by norm_num) hbal
