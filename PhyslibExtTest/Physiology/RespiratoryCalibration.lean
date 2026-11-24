/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.Physiology.RespiratoryCalibration

/-! Tests: proportional columns at a single sample. -/

namespace PhyslibExtTest.Physiology.RespiratoryCalibration

open PhyslibExt.Physiology.RespiratoryCalibration

/-- With `vp = 2 * v`, `(0, 0)` and `(1, -2)` give the same datum. -/
example : (fun _ : Unit => (2:ℝ)) () * (0 + 1) + (fun _ : Unit => (1:ℝ)) () * (0 - 2 * 1) =
    (fun _ : Unit => (2:ℝ)) () * 0 + (fun _ : Unit => (1:ℝ)) () * 0 :=
  resp_proportional_same_data (fun _ => (2:ℝ)) (fun _ => (1:ℝ)) 2 0 0 1 (fun _ => by norm_num) ()

/-- The calibration map is not injective on the two-point domain. -/
example :
    ¬ Set.InjOn (fun p : ℝ × ℝ => fun _ : Unit =>
      (fun _ : Unit => (2:ℝ)) () * p.1 + (fun _ : Unit => (1:ℝ)) () * p.2)
      ({((0, 0) : ℝ × ℝ), ((1, -2) : ℝ × ℝ)} : Set (ℝ × ℝ)) :=
  resp_proportional_not_injective (fun _ => (2:ℝ)) (fun _ => (1:ℝ)) 2 0 0 1
    (fun _ => by norm_num) one_ne_zero _ (by simp) (by simp)

end PhyslibExtTest.Physiology.RespiratoryCalibration
