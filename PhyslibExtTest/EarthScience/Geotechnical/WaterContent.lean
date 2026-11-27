/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.Geotechnical.WaterContent
import Mathlib.Tactic.NormNum

/-!
# Water-content checks

Focused checks for `PhyslibExt.EarthScience.Geotechnical.WaterContent`:
dry soil (`Vw = 0`) gives `S = 0` and both sides 0; saturated soil
(`Vw = Vv`) gives `S = 1`, hence `e = w_g * G_s`.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- Dry case: both sides vanish. -/
example : degreeOfSaturation 0 2 * voidRatio 1 2
    = gravimetricWaterContent (1000 * 0) (2650 * 1)
      * specificGravity 2650 1000 := by
  have h := saturation_mul_voidRatio (Vs := 1) (Vv := 2) (Vw := 0)
    (ρs := 2650) (ρw := 1000) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  rw [h]

/-- Saturated case: `S = 1`. -/
example : degreeOfSaturation 2 2 = 1 := by
  simp [degreeOfSaturation]
