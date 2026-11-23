/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Epidemiology.IncidenceObservation.Intensity

/-! Tests: constant trajectory intensity and zero width. -/

namespace MathlibExtTest.Biology.Epidemiology.IncidenceObservation.Intensity

open MathlibExt.Biology.Epidemiology.IncidenceObservation.Intensity

/-- Constant `S = I = 1`, `beta = 1`, `N = 2`, window `[0, 2]`:
intensity `rho * 1 + background * 2 ≥ 0`. -/
example : 0 ≤ (1/2 : ℝ) * (∫ _t in (0:ℝ)..2, 1 * 1 * 1 / 2) + (1/4) * (2 - 0) :=
  incidence_nonneg (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) continuous_const continuous_const
    (fun _ => by norm_num) (fun _ => by norm_num)

/-- Zero-width window. -/
example (rho background : ℝ) :
    rho * (∫ _t in (1:ℝ)..1, 2 * 1 * 1 / 3) + background * (1 - 1) = 0 :=
  incidence_zero_width

end MathlibExtTest.Biology.Epidemiology.IncidenceObservation.Intensity
