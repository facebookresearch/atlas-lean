/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Resource.ReservoirBalance

import Mathlib.Tactic.NormNum

/-!
# Tests for reservoir inventory

Boundary checks for `PhyslibExt.Engineering.Resource.ReservoirBalance`:
unit parameters depleted to `p = -1` produce `1 - exp (-1)` and recover
the pore volume; no pressure change produces nothing; injection is
negative production.
-/

namespace Engineering.Resource.ReservoirBalance.Tests

open Engineering.Resource.ReservoirBalance

-- rho0 = cfl = Vp = 1, p0 = 0, p = -1: produced mass 1 - exp (-1),
-- positive.
example : producedMass 1 1 1 0 (-1) = 1 - Real.exp (-1) := by
  rw [produced_mass_eq]
  norm_num

example : 0 < producedMass 1 1 1 0 (-1) := by
  exact produced_mass_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- The same fixture recovers Vp = 1 through the identification formula.
example : (1 : ℝ) = producedMass 1 1 1 0 (-1) /
    (1 * (1 - Real.exp (1 * (-1 - 0)))) := by
  exact porevolume_identified (by norm_num) (by norm_num) (by norm_num) rfl

-- At p = p0 both density change and production vanish.
example : producedMass 3 2 1 5 5 = 0 := by
  exact produced_mass_zero_at_initial _ _ _ _

-- Injection sign: pressure above initial gives negative produced mass.
example : producedMass 1 1 1 0 1 < 0 := by
  exact produced_mass_neg_of_pressure_increase (by norm_num) (by norm_num) (by norm_num) (by norm_num)

end Engineering.Resource.ReservoirBalance.Tests
