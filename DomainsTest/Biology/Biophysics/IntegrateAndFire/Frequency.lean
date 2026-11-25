/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.IntegrateAndFire.Frequency

/-! Tests: period positivity and frequency monotonicity instances. -/

namespace MathlibExtTest.Biology.Biophysics.IntegrateAndFire.Frequency

open MathlibExt.Biology.Biophysics.IntegrateAndFire.Frequency

/-- Period at `tau = 2`, `ur = 0`, `theta = 1`, `uinf = 3`. -/
example : 0 < lifPeriod 2 0 1 3 :=
  lifPeriod_pos (by norm_num) (by norm_num) (by norm_num)

/-- Frequency strictly increases between drives `uinf = 2` and `3`
(compare values via the StrictMonoOn statement at two points). -/
example : (fun uinf => 1 / (lifPeriod 2 0 1 uinf + 0)) 2 <
    (fun uinf => 1 / (lifPeriod 2 0 1 uinf + 0)) 3 :=
  lif_frequency_strictMonoOn (tau := 2) (ur := 0) (theta := 1) (tref := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.Biology.Biophysics.IntegrateAndFire.Frequency
