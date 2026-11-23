/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.RMSAveragePower
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Circuits.RMSAveragePower

namespace PhyslibExtTest.Circuits.RMSAveragePower

/-- A unit real phasor against itself averages to `1` over a full
period, for `omega = 2` starting at `0`. -/
example : (∫ t in (0:ℝ)..(0 + 2 * Real.pi / 2),
      rmsWaveform 1 2 t * rmsWaveform 1 2 t) / (2 * Real.pi / 2) = 1 := by
  have h := average_rmsWaveform_mul_self (1 : ℂ) (ω := 2) (by norm_num) 0
  simpa using h

/-- A quadrature waveform averages to zero against the original. -/
example : (∫ t in (0:ℝ)..(0 + 2 * Real.pi / 2),
      rmsWaveform 1 2 t * rmsWaveform (Complex.I * 1) 2 t)
      / (2 * Real.pi / 2) = 0 := by
  have h := average_rmsWaveform_mul_quadrature (1 : ℂ) (ω := 2) (by norm_num) 0
  simpa using h

/-- The peak-waveform average at the same values is `1/2`. -/
example : (∫ t in (0:ℝ)..(0 + 2 * Real.pi / 2),
      peakWaveform 1 2 t * peakWaveform 1 2 t) / (2 * Real.pi / 2)
    = 1 / 2 := by
  have h := average_peakWaveform_mul_peakWaveform (1 : ℂ) (1 : ℂ) (ω := 2)
    (by norm_num) 0
  simpa using h

/-- Waveform values at `t = 0` through the public lemmas. -/
example : rmsWaveform (3 + 4 * Complex.I) 2 0 = Real.sqrt 2 * 3 := by
  simp [rmsWaveform_at_zero]

example : peakWaveform (3 + 4 * Complex.I) 2 0 = 3 := by
  simp [peakWaveform_at_zero]

end PhyslibExtTest.Circuits.RMSAveragePower
