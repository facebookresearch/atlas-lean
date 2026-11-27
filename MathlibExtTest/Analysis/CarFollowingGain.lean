/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import MathlibExt.Analysis.CarFollowingGain

/-!
# Car-following gain checks

Focused checks for `MathlibExt.Analysis.CarFollowingGain`: at
`T = 0` the criterion holds for every positive frequency, through
the public equivalence.

These are elaboration and non-vacuity checks, not new results.
-/

open CarFollowingGain

/-- Zero delay: gain reduction holds (the criterion is `w > 0`). -/
example (w : ℝ) (hw : 0 < w) :
    ‖(1 : ℂ) * Complex.exp (-(Complex.I * w * 0))‖ < ‖denom 1 0 w‖ :=
  (gain_lt_one_iff (lam := 1) (T := 0) (w := w) (by norm_num) hw).mpr (by
    simp [hw])
