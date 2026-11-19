/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Biophysics.IntegrateAndFire.Trajectory

/-! Tests: event gaps at unit durations. -/

namespace MathlibExtTest.Biology.Biophysics.IntegrateAndFire.Trajectory

open MathlibExt.Biology.Biophysics.IntegrateAndFire.Trajectory

/-- Gap at `T = 1`, `tref = 0`, dose index `3` is `1`. -/
example : ((3 + 1 : ℕ) : ℝ) * (1 + 0) - (3 : ℝ) * (1 + 0) = (1:ℝ) :=
  lif_event_gap_zero_refractory 3

end MathlibExtTest.Biology.Biophysics.IntegrateAndFire.Trajectory
