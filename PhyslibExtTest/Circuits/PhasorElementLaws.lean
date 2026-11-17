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

end PhyslibExtTest.Circuits.PhasorElementLaws
