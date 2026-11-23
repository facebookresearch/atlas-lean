/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.Geotechnical.PhaseRelations

/-!
# Soil phase-relation checks

Concrete consumers of `PhyslibExt.EarthScience.Geotechnical.PhaseRelations`:
solid volume `2` and void volume `1` give void ratio `1 / 2` and porosity
`1 / 3`; the dry and equal-volume cases give porosity `0` and `1 / 2`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. A nonzero phase element
- B. Boundary cases
- C. Public theorem shape

## iv. References

- `PhyslibExt.EarthScience.Geotechnical.PhaseRelations`
-/

open EarthScience

/-! ## A. A nonzero phase element -/

/-- For `Vs = 2`, `Vv = 1`: `e = 1 / 2` and `n = 1 / 3 = e / (1 + e)`. -/
example : voidRatio 2 1 = 1 / 2 ∧ porosity 2 1 = 1 / 3 := by
  constructor <;> norm_num [voidRatio, porosity]

/-- The normalization theorem at `Vs = 2`, `Vv = 1`. -/
example : porosity 2 1 = voidRatio 2 1 / (1 + voidRatio 2 1) :=
  porosity_eq_voidRatio_div_one_add_voidRatio (by norm_num) (by norm_num)

/-! ## B. Boundary cases -/

/-- No voids: both coordinates are `0`. -/
example : voidRatio 2 0 = 0 ∧ porosity 2 0 = 0 := by
  constructor <;> norm_num [voidRatio, porosity]

/-- Equal solid and void volumes: `e = 1`, `n = 1 / 2`. -/
example : voidRatio 3 3 = 1 ∧ porosity 3 3 = 1 / 2 := by
  constructor <;> norm_num [voidRatio, porosity]

/-- Porosity bounds at the nonzero witness. -/
example : 0 ≤ porosity 2 1 ∧ porosity 2 1 < 1 :=
  ⟨porosity_nonneg (by norm_num) (by norm_num),
   porosity_lt_one (by norm_num) (by norm_num)⟩

/-! ## C. Public theorem shape -/

/-- The public statements, restated through the definitions. -/
example {Vs Vv : ℝ} (hVs : 0 < Vs) (hVv : 0 ≤ Vv) :
    Vv / (Vs + Vv) = (Vv / Vs) / (1 + Vv / Vs) :=
  porosity_eq_voidRatio_div_one_add_voidRatio hVs hVv
