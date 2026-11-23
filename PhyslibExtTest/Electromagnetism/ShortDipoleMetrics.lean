/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electromagnetism.ShortDipoleMetrics
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Electromagnetism.ShortDipoleMetrics

namespace PhyslibExtTest.Electromagnetism.ShortDipoleMetrics

/-- Total radiated power at unit drive is `8π/3`. -/
example : radiatedPower (shortDipoleIntensity 1) = 8 * Real.pi * 1 / 3 :=
  radiatedPower_shortDipoleIntensity 1 (by norm_num)

/-- Broadside directivity attains the maximum `3/2`. -/
example : directivity (shortDipoleIntensity 1) (Real.pi / 2) = 3 / 2 := by
  have h := directivity_shortDipoleIntensity 1 (by norm_num) (Real.pi / 2)
  rw [h]
  simp

/-- On-axis directivity is zero at both poles. -/
example : directivity (shortDipoleIntensity 1) 0 = 0
    ∧ directivity (shortDipoleIntensity 1) Real.pi = 0 :=
  directivity_shortDipoleIntensity_on_axis 1 (by norm_num)

/-- Zero drive radiates nothing. -/
example : radiatedPower (shortDipoleIntensity 0) = 0 :=
  radiatedPower_shortDipoleIntensity_zero

end PhyslibExtTest.Electromagnetism.ShortDipoleMetrics
