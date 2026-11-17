/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic

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
* `sensor_calibrate_apply`: the identity at every visit of a design.

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
  have hcancel : g * H / g = H := mul_div_cancel_left₀ H hg
  rw [add_right_comm, add_sub_cancel_right, add_div, hcancel]

/-- The calibrated value at every visit of a fixed design: for
observations `y j = g * H j + offset + ε j`, `(y j - offset) / g =
H j + ε j / g` for all `j`. -/
lemma sensor_calibrate_apply {ι : Type*} {g offset : ℝ} (hg : g ≠ 0)
    (H ε : ι → ℝ) (j : ι) :
    (g * H j + offset + ε j - offset) / g = H j + ε j / g := by
  exact sensor_calibrate hg

end PhyslibExt.BiomedicalInstrumentation.CalibrationObservation
