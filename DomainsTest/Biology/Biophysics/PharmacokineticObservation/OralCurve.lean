/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.PharmacokineticObservation.OralCurve

/-! Tests: scaling invariance and flip-flop at numeric parameters. -/

namespace MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.OralCurve

open MathlibExt.Biology.Biophysics.PharmacokineticObservation.OralCurve

/-- Scaling by `s = 2` preserves the curve at `t = 1`. -/
example : (1:ℝ) * 10 * 2 * (Real.exp (-(2 / 5) * 1) - Real.exp (-2 * 1)) / (5 * (2 - 2 / 5)) =
    (1 * 2) * 10 * 2 * (Real.exp (-((2 * 2) / (5 * 2)) * 1) - Real.exp (-2 * 1)) /
      ((5 * 2) * (2 - (2 * 2) / (5 * 2))) :=
  oral_scaling_curve (by norm_num) (by norm_num) (by norm_num)

/-- Physical flip-flop: `(1, 10, 1, 5, 10)` maps to the flipped
tuple with bioavailability `1 * 1 / (10 / 5) = 1 / 2`. -/
example : (1:ℝ) * 10 * 1 * (Real.exp (-(10 / 5) * 1) - Real.exp (-1 * 1)) /
      (5 * (1 - 10 / 5)) =
    (1 * 10 * (10 / 5) * (Real.exp (-1 * 1) - Real.exp (-(10 / 5) * 1)) *
      (1 / (10 / 5))) / (5 * (10 / 5 - 1)) :=
  (oral_flip_flop (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)).1

end MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.OralCurve
