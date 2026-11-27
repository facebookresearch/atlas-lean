/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.UnitWeights
import Mathlib.Tactic.NormNum

/-!
# Unit-weight checks

Focused checks for `PhyslibExt.EarthScience.Geotechnical.UnitWeights`:
a standard saturated soil (`Gs = 2.65`, `e = 1`) has positive
submerged weight, and a light solid (`Gs = 0.5`) does not.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Standard saturated soil: submerged weight is positive. -/
example : 0 < submergedUnitWeight 2.65 1 9.81 :=
  (submerged_pos_iff (by norm_num) (by norm_num)).2 (by norm_num)

/-- Light solid: submerged weight is not positive. -/
example : ¬ 0 < submergedUnitWeight 0.5 1 9.81 := by
  rw [submerged_pos_iff (by norm_num) (by norm_num)]
  norm_num
