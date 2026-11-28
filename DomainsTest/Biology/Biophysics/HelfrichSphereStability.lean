/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Biophysics.HelfrichSphereStability
import Mathlib.Tactic.NormNum

/-! # Tests for the zero mode of the Helfrich sphere -/

namespace DomainsTest.Biology.Biophysics.HelfrichSphereStability

open WantedExt.Biology.Biophysics.HelfrichSphereStabilityWanted

-- For k_c = 3, c₀ = -1, R = 2, the lower pressure threshold is 3/2, not p_c = 6.
example : criticalPressure 3 (-1) 2 = 6 ∧
    criticalPressure 3 (-1) 2 - 12 * 3 / 2 ^ 3 = 3 / 2 := by
  norm_num [criticalPressure.eq_def]

-- Evaluate the coefficient directly below, at, and above the threshold.
example : modeCoeff 3 (-1) 2 1 0 = -1 ∧ modeCoeff 3 (-1) 2 (3 / 2) 0 = 0 ∧
    modeCoeff 3 (-1) 2 2 0 = 1 := by
  norm_num [modeCoeff.eq_def]

-- Compare both sides of the pressure criterion without using the new theorem.
example : (0 ≤ modeCoeff 3 (-1) 2 1 0 ↔ criticalPressure 3 (-1) 2 - 12 * 3 / 2 ^ 3 ≤ 1) ∧
    (0 ≤ modeCoeff 3 (-1) 2 (3 / 2) 0 ↔ criticalPressure 3 (-1) 2 - 12 * 3 / 2 ^ 3 ≤ 3 / 2) ∧
    (0 ≤ modeCoeff 3 (-1) 2 2 0 ↔ criticalPressure 3 (-1) 2 - 12 * 3 / 2 ^ 3 ≤ 2) := by
  norm_num [modeCoeff.eq_def, criticalPressure.eq_def]

-- A client can use the pressure criterion without evaluating the coefficient.
example : 0 ≤ modeCoeff 3 (-1) 2 2 0 := by
  refine (modeCoeff_zero 3 (-1) 2 2 (hkc := by norm_num) (hR := by norm_num)).2.mpr ?_
  norm_num [criticalPressure.eq_def]

end DomainsTest.Biology.Biophysics.HelfrichSphereStability
