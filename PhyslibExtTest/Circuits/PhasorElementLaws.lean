/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Circuits.PhasorElementLaws

@[expose] public section

open PhyslibExt.Circuits.PhasorElementLaws PhyslibExt.Circuits.RMSAveragePower

namespace PhyslibExtTest.Circuits.PhasorElementLaws

/-- The three element laws at zero phasors with the canonical
RMS waveforms. -/
example {ω : ℝ} (hω : 0 < ω) :
    ((∀ t, rmsWaveform 0 ω t = 2 * rmsWaveform 0 ω t) ↔ (0 : ℂ) = (2 : ℂ) * 0) ∧
      ((∀ t, rmsWaveform 0 ω t = 3 * deriv (rmsWaveform 0 ω) t) ↔
        (0 : ℂ) = Complex.I * (ω : ℂ) * (3 : ℂ) * 0) ∧
      ((∀ t, rmsWaveform 0 ω t = 5 * deriv (rmsWaveform 0 ω) t) ↔
        (0 : ℂ) = Complex.I * (ω : ℂ) * (5 : ℂ) * 0) :=
  phasor_element_laws 2 3 5 (by norm_num) (by norm_num) (by norm_num) hω 0 0
    (rmsWaveform 0 ω) (rmsWaveform 0 ω) (fun _ => rfl) (fun _ => rfl)

/-- Nonzero inductor case: `V = 6i`, `I = 1`, `L = 2`, `omega = 3`
satisfies the phasor law, its waveform vanishes at `t = 0`, and at
a quarter period it reads `sqrt 2 * (-6)`. -/
example : (Complex.I * (3 : ℂ) * (2 : ℂ) * 1) = 6 * Complex.I := by ring

/-- The inductor law at nonzero values, through the public iff. -/
example :
    ((∀ t, rmsWaveform (6 * Complex.I) 3 t = 2 * deriv (rmsWaveform 1 3) t) ↔
      (6 * Complex.I : ℂ) = Complex.I * (3 : ℂ) * (2 : ℂ) * 1) :=
  inductor_law_iff_phasor 2 (by norm_num) (by norm_num) (6 * Complex.I) 1
    (rmsWaveform (6 * Complex.I) 3) (rmsWaveform 1 3) (fun _ => rfl) (fun _ => rfl)

/-- Quarter-period lead at nonzero values: the voltage waveform
is `omega L` times the current waveform advanced by a quarter
period. -/
example (t : ℝ) :
    rmsWaveform (6 * Complex.I) 3 t =
      3 * 2 * rmsWaveform 1 3 (t + Real.pi / (2 * 3)) :=
  inductor_voltage_leads_current 2 (by norm_num) (by norm_num) (6 * Complex.I) 1 (by push_cast; ring) t

/-- A nonzero admittance case: `R = 2`, `V = 2`, `I = 1`
satisfies the admittance form `I = V / R`. -/
example : ((2 : ℂ) = (2 : ℂ) * 1) ↔ (1 : ℂ) = (2 : ℂ) / (2 : ℂ) :=
  resistor_phasor_iff_admittance 2 (by norm_num) 2 1


end PhyslibExtTest.Circuits.PhasorElementLaws
