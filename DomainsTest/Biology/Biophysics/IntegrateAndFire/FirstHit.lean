/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.IntegrateAndFire.FirstHit

/-! Tests for the LIF first hit: a numerical trajectory checked at its
hit time and before it, and the subthreshold no-hit case. -/

namespace MathlibExtTest.Biology.Biophysics.IntegrateAndFire.FirstHit

open MathlibExt.Biology.Biophysics.IntegrateAndFire.FirstHit
open Filter Topology

/-- `ur = 0`, `theta = 1`, `tau = 2`, `uinf = 3`: the hit time is
positive and the trajectory equals `1` there. -/
example : let T := 2 * Real.log ((3 - 0) / (3 - 1))
    0 < T ∧ 3 - (3 - 0) * Real.exp (-T / 2) = 1 := by
  have h := lif_first_hit (ur := 0) (theta := 1) (tau := 2) (uinf := 3)
    (by norm_num) (by norm_num) (by norm_num)
  exact ⟨h.1, h.2.1⟩

/-- Subthreshold `uinf = theta = 1`: no finite hit. -/
example : ∀ t : ℝ, 0 ≤ t → 1 - (1 - 0) * Real.exp (-t / 2) < 1 :=
  lif_no_hit (ur := 0) (theta := 1) (tau := 2) (uinf := 1)
    (by norm_num) (by norm_num) (le_refl 1)

/-- Before the hit: at `t = 0` the trajectory is at the reset `0 < 1`. -/
example : (3:ℝ) - (3 - 0) * Real.exp (-(0:ℝ) / 2) < 1 := by
  have h := lif_first_hit (ur := 0) (theta := 1) (tau := 2) (uinf := 3)
    (by norm_num) (by norm_num) (by norm_num)
  exact h.2.2 0 (le_refl 0) h.1

/-- At threshold equilibrium the trajectory tends to `theta`. -/
example : Filter.Tendsto (fun t => (1:ℝ) - (1 - 0) * Real.exp (-t / 2))
    Filter.atTop (𝓝 1) :=
  lif_tendsto (by norm_num)

end MathlibExtTest.Biology.Biophysics.IntegrateAndFire.FirstHit
