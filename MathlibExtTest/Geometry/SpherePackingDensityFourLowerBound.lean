/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Geometry.SpherePackingDensityFourLowerBound

namespace MathlibExtTest.Geometry.SpherePackingDensityFourLowerBound

open MathlibExt.Geometry.SpherePackingDensityFourWanted

example : ENNReal.ofReal (Real.pi ^ 2 / 16) ≤ spherePackingDensity4 :=
  lowerBound_dLOV2014_wanted

-- Dividing by the volume of a unit ball recovers the center density in Table 1.
example : ENNReal.ofReal (1 / 8) ≤ centerDensity4 := by
  rw [centerDensity4, ENNReal.le_div_iff_mul_le (Or.inl unitBallVolume4_ne_zero)
    (Or.inl unitBallVolume4_ne_top), unitBallVolume4_eq, ← ENNReal.ofReal_mul (by norm_num)]
  rw [show (1 / 8 : ℝ) * (Real.pi ^ 2 / 2) = Real.pi ^ 2 / 16 by ring]
  exact lowerBound_dLOV2014_wanted

end MathlibExtTest.Geometry.SpherePackingDensityFourLowerBound
