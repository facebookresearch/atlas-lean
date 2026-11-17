/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import PhyslibExt.EarthScience.Calibration

/-!
# Sensor calibration observation

## i. Overview

For an observation `y = g * H + offset + ε` with known nonzero gain
`g` and known offset, the calibrated value `(y - offset) / g` recovers
exactly `H + ε / g`: calibration recovers the measured quantity `H`
plus scaled noise, not the hidden state behind `H` (which need not be
recoverable, since `H` need not be injective). Zero gain is excluded;
an unknown or zero gain confounds amplitude.

## ii. Key results

* `sensor_calibrate`: the pointwise calibration identity.
* The per-visit form is ordinary specialization of `sensor_calibrate`.
  The pointwise core is `EarthScience.calibration_estimator_error`,
  reused rather than duplicated.

## iii. Table of contents

* A. Calibration identity.

## iv. References

* The declared observation model is local to this module; both
  declarations are `lemma`s.

-/

@[expose] public section

namespace PhyslibExt.BiomedicalInstrumentation.CalibrationObservation

/-! ## A. Calibration identity. -/

/-- **Sensor calibration identity.** For an observation
`y = g * H + offset + ε` with known nonzero gain `g` and known
offset, the calibrated value `(y - offset) / g` recovers exactly
`H + ε / g`: calibration recovers the measured quantity `H` (plus
scaled noise), not the hidden state behind `H`. Zero gain is
excluded: an unknown or zero gain confounds amplitude. -/
lemma sensor_calibrate {g offset H ε : ℝ} (hg : g ≠ 0) :
    (g * H + offset + ε - offset) / g = H + ε / g := by
  have h := EarthScience.calibration_estimator_error hg (x := H) (ε := ε)
    (b := offset) (a := g)
  linarith


end PhyslibExt.BiomedicalInstrumentation.CalibrationObservation
