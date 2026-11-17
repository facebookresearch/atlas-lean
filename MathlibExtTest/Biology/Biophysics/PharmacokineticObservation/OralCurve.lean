/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.PharmacokineticObservation.OralCurve

/-! Tests: scaling invariance and flip-flop at numeric parameters. -/

namespace MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.OralCurve

open MathlibExt.Biology.Biophysics.PharmacokineticObservation.OralCurve

/-- Scaling by `s = 2` preserves the curve at `t = 1`. -/
example : (1:ℝ) * 10 * 2 * (Real.exp (-(2 / 5) * 1) - Real.exp (-2 * 1)) / (5 * (2 - 2 / 5)) =
    (1 * 2) * 10 * 2 * (Real.exp (-((2 * 2) / (5 * 2)) * 1) - Real.exp (-2 * 1)) /
      ((5 * 2) * (2 - (2 * 2) / (5 * 2))) :=
  oral_scaling_curve (by norm_num) (by norm_num) (by norm_num)

/-- Flip-flop with `A = 3`, `ka = 2`, `k = 1`, `t = 1`. -/
example : (3:ℝ) * (Real.exp (-1 * 1) - Real.exp (-2 * 1)) / (2 - 1) =
    3 * (Real.exp (-2 * 1) - Real.exp (-1 * 1)) / (1 - 2) :=
  oral_flip_flop

end MathlibExtTest.Biology.Biophysics.PharmacokineticObservation.OralCurve
