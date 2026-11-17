/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.BiomedicalInstrumentation.CalibrationObservation
import Mathlib.Data.Fin.VecNotation

/-! Tests for the calibration identity: nonzero gain/offset, negative
gain, and per-visit application. -/

namespace PhyslibExtTest.BiomedicalInstrumentation.CalibrationObservation

open PhyslibExt.BiomedicalInstrumentation.CalibrationObservation Matrix
open scoped Matrix

/-- `g = 2`, `offset = 3`, `H = 5`, `ε = 1/2`: calibrated value is
`5 + 1/4`. -/
example : ((2 : ℝ) * 5 + 3 + 1/2 - 3) / 2 = 5 + (1/2) / 2 :=
  sensor_calibrate (by norm_num)

/-- Negative gain `g = -2`: the identity still holds. -/
example : ((-2 : ℝ) * 5 + 3 + 1 - 3) / (-2) = 5 + 1 / (-2) :=
  sensor_calibrate (by norm_num)

/-- Per-visit application on a two-visit design. -/
example (j : Fin 2) :
    ((4:ℝ) * ![5, 7] j + 1 + ![0, 2] j - 1) / 4 = ![5, 7] j + ![0, 2] j / 4 :=
  sensor_calibrate_apply (g := 4) (offset := 1) (by norm_num) ![5, 7] ![0, 2] j

end PhyslibExtTest.BiomedicalInstrumentation.CalibrationObservation
