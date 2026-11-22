/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.GibbsEnergyMinimization

/-!
# Gibbs-energy minimisation checks

Concrete consumers of
`PhyslibExt.EarthScience.GibbsEnergyMinimization`: the two-phase
minimisation with `N = 2`, `μ₁ = 1`, `μ₂ = 3`, the strict version, and
the degenerate equal-potential case.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`n₁ = 1 / 2`, `G(1 / 2) = 1 / 2 * 1 + 3 / 2 * 3 = 5`, while the
all-phase-1 split gives `G(2) = 2`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Gibbs minimisation with numbers

## iv. References

- `PhyslibExt.EarthScience.GibbsEnergyMinimization`
-/

/-- Minimisation with numbers: `G(1 / 2) = 5 ≥ 2 = G(2)`. -/
example : (2 : ℝ) * 1 ≤ (1 / 2) * 1 + (2 - 1 / 2) * 3 :=
  EarthScience.gibbs_min_two_phase (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Strict version with numbers: `2 < 5`. -/
example : (2 : ℝ) * 1 < (1 / 2) * 1 + (2 - 1 / 2) * 3 :=
  EarthScience.gibbs_min_two_phase_strict (by norm_num) (by norm_num)
    (by norm_num)

/-- Equal potentials: every split has `G = 4` for `N = 2`, `μ = 2`. -/
example : (1 / 2 : ℝ) * 2 + (2 - 1 / 2) * 2 = 2 * 2 :=
  EarthScience.gibbs_min_equal_potentials rfl
