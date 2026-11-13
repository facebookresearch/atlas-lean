/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.DewpointInversion

/-!
# Dewpoint-inversion checks

Concrete consumers of `PhyslibExt.EarthScience.DewpointInversion`:
with `es0 = 6.11`, `L = 5423`, `Rv = 1`, `T0 = 273.15`, distinct
temperatures `279` and `280` give distinct saturation pressures, so no
two distinct positive temperatures invert to the same dewpoint; and a
temperature inverting to the pressure at `280` must itself be `280`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Distinct temperatures, distinct pressures
- B. Inversion recovers the temperature

## iv. References

- `PhyslibExt.EarthScience.DewpointInversion`
-/

/-- Public shape of the dewpoint-inversion uniqueness theorem. -/
example {es0 L Rv T0 : ℝ} (hes0 : 0 < es0) (hL : 0 < L) (hRv : 0 < Rv)
    {T₁ T₂ : ℝ} (hT₁ : 0 < T₁) (hT₂ : 0 < T₂)
    (h : es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T₁))
      = es0 * Real.exp ((L / Rv) * (1 / T0 - 1 / T₂))) :
    T₁ = T₂ :=
  EarthScience.dewpoint_inversion_unique hes0 hL hRv hT₁ hT₂ h

/-- Distinct temperatures give distinct saturation pressures:
`es(279) ≠ es(280)`. -/
example :
    (6.11 : ℝ) * Real.exp ((5423 / 1 : ℝ) * (1 / 273.15 - 1 / 279))
      ≠ (6.11 : ℝ) * Real.exp ((5423 / 1 : ℝ) * (1 / 273.15 - 1 / 280)) := by
  intro heq
  have h := EarthScience.dewpoint_inversion_unique (es0 := (6.11 : ℝ)) (L := (5423 : ℝ))
    (Rv := (1 : ℝ)) (T0 := (273.15 : ℝ)) (T₁ := (279 : ℝ)) (T₂ := (280 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) heq
  norm_num at h

/-- Distinct temperatures give distinct saturation pressures:
`es(280) ≠ es(281)`. -/
example :
    (6.11 : ℝ) * Real.exp ((5423 / 1 : ℝ) * (1 / 273.15 - 1 / 280))
      ≠ (6.11 : ℝ) * Real.exp ((5423 / 1 : ℝ) * (1 / 273.15 - 1 / 281)) := by
  intro heq
  have h := EarthScience.dewpoint_inversion_unique (es0 := (6.11 : ℝ)) (L := (5423 : ℝ))
    (Rv := (1 : ℝ)) (T0 := (273.15 : ℝ)) (T₁ := (280 : ℝ)) (T₂ := (281 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) heq
  norm_num at h

/-- Inversion recovers the temperature: if `es(T) = es(280)` and
`T > 0`, then `T = 280`. -/
example {T : ℝ} (hT : 0 < T)
    (h : (6.11 : ℝ) * Real.exp ((5423 / 1 : ℝ) * (1 / 273.15 - 1 / T))
      = (6.11 : ℝ) * Real.exp ((5423 / 1 : ℝ) * (1 / 273.15 - 1 / 280))) :
    T = 280 :=
  EarthScience.dewpoint_inversion_unique (es0 := (6.11 : ℝ)) (L := (5423 : ℝ))
    (Rv := (1 : ℝ)) (T0 := (273.15 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
    hT (by norm_num) h
