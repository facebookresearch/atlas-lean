/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.ElasticSeismicWaves

/-!
# Elastic seismic wave checks

Concrete consumers of `PhyslibExt.EarthScience.ElasticSeismicWaves`:
`K = 12`, `μ = 9`, `ρ = 3` (so `cP ^ 2 = 8`, `cS ^ 2 = 3`), a plane wave
with `k = 2`, `ω = 6`, and the zero-modulus boundary.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Numeric speeds
- B. Plane wave and dispersion
- C. Zero-modulus boundary

## iv. References

- `PhyslibExt.EarthScience.ElasticSeismicWaves`
-/

/-- Numeric P-wave speed squared: `(12 + 4 * 9 / 3) / 3 = 8`. -/
example : (Real.sqrt ((12 + 4 * (9 : ℝ) / 3) / 3)) ^ 2 = 8 := by
  rw [EarthScience.elastic_p_wave_speed_sq (K := 12) (μ := 9) (ρ := 3)
    (by norm_num) (by norm_num) (by norm_num)]
  norm_num

/-- Numeric S-wave speed squared: `9 / 3 = 3`. -/
example : (Real.sqrt ((9 : ℝ) / 3)) ^ 2 = 3 := by
  rw [EarthScience.elastic_s_wave_speed_sq (μ := 9) (ρ := 3) (by norm_num) (by norm_num)]
  norm_num

/-- Numeric ordering: S speed below P speed. -/
example : Real.sqrt ((9 : ℝ) / 3) < Real.sqrt ((12 + 4 * 9 / 3) / 3) :=
  EarthScience.elastic_p_faster_than_s (by norm_num) (by norm_num) (by norm_num)

/-- Plane wave: first time derivative at `k = 2`, `ω = 6`, `x = 0`, `t = 0`. -/
example : HasDerivAt (fun t => Real.cos (2 * (0 : ℝ) - 6 * t))
    (6 * Real.sin (2 * 0 - 6 * (0 : ℝ))) 0 :=
  EarthScience.hasDerivAt_planeWave_time

/-- Plane wave: second time derivative at `k = 2`, `ω = 6`, `x = 0`, `t = 0`. -/
example : HasDerivAt (fun t => 6 * Real.sin (2 * (0 : ℝ) - 6 * t))
    (-(6 : ℝ) ^ 2 * Real.cos (2 * 0 - 6 * (0 : ℝ))) 0 :=
  EarthScience.hasDerivAt_planeWave_time2

/-- Dispersion `6 ^ 2 = 3 ^ 2 * 2 ^ 2` gives the wave equation on
second-derivative values. -/
example : -(6 : ℝ) ^ 2 * Real.cos (2 * (0 : ℝ) - 6 * 0)
    = 3 ^ 2 * (-(2 : ℝ) ^ 2 * Real.cos (2 * 0 - 6 * (0 : ℝ))) :=
  EarthScience.planeWave_waveEquation (by norm_num)

/-- Zero-modulus boundary: `K = μ = 0` gives zero P-wave speed squared. -/
example : (Real.sqrt (((0 : ℝ) + 4 * 0 / 3) / 3)) ^ 2 = 0 := by
  rw [EarthScience.elastic_p_wave_speed_sq (K := 0) (μ := 0) (ρ := 3)
    (le_refl 0) (le_refl 0) (by norm_num)]
  norm_num
