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

-- Distinct parameter pairs with the same product give identical
-- linearized histories at every pressure: individual parameters are not
-- identified.
example (p : ℝ) :
    linearProducedMass 2 1 3 0 p = linearProducedMass 1 1 6 0 p ∧
      ((2 : ℝ), (3 : ℝ)) ≠ (1, 6) := by
  refine ⟨linear_identifies_only_product (by norm_num), by norm_num⟩

-- The identification converse itself under both nondegeneracy guards:
-- equal linearized observations at a nonzero pressure excursion recover
-- the product equality, through `linearProducedMass_eq_iff`.
example (h : linearProducedMass 2 1 3 0 1 =
    linearProducedMass 1 1 6 0 1) : (2 : ℝ) * 3 = 1 * 6 := by
  exact (linearProducedMass_eq_iff (by norm_num) (by norm_num)).mp h

-- Both guards are necessary. With zero reference density every
-- linearized observation is zero, so distinct products agree.
example : linearProducedMass 2 0 3 0 1 = linearProducedMass 1 0 5 0 1 ∧
    ¬ ((2 : ℝ) * 3 = 1 * 5) := by
  refine ⟨by simp [linearProducedMass], by norm_num⟩

-- With no pressure excursion every linearized observation is also zero.
example : linearProducedMass 2 1 3 0 0 = linearProducedMass 1 1 5 0 0 ∧
    ¬ ((2 : ℝ) * 3 = 1 * 5) := by
  refine ⟨by simp [linearProducedMass], by norm_num⟩

end Engineering.Resource.ReservoirBalance.Tests
