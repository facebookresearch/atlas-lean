/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.BiomedicalImaging.CTAttenuation

/-! Tests: attenuation at unit incident intensity. -/

namespace PhyslibExtTest.BiomedicalImaging.CTAttenuation

open PhyslibExt.BiomedicalImaging.CTAttenuation

/-- At `I0 = 1` and `L = 2`, log attenuation recovers `2`. -/
example : Real.log (1 / (1 * Real.exp (-(2:ℝ)))) = 2 :=
  attenuation_log_ratio one_pos

/-- The mixture transmission differs from the mean attenuation. -/
example : -Real.log ((Real.exp (0:ℝ) + Real.exp (-2)) / 2) ≠ 1 :=
  mixture_log_ne_mean

end PhyslibExtTest.BiomedicalImaging.CTAttenuation
