/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Resource.PorousStorage

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum


/-!
# Tests for porous storage inventory

Pore volume 2 at phi = 1/4, V_bulk = 8; saturations (1/4, 3/4), densities (1, 2).
-/

namespace Engineering.Resource.PorousStorage.Tests

open Engineering.Resource.PorousStorage

/-- Two-phase saturations `(1/4, 3/4)`. -/
noncomputable def S2 : Fin 2 → ℝ := ![1 / 4, 3 / 4]

/-- Two-phase densities `(2, 1)`. -/
def rho2 : Fin 2 → ℝ := ![2, 1]

-- The partition theorem itself, at porosity 1 and bulk volume 8.
example : ∑ i, phaseVolume 1 8 S2 i = poreVolume 1 8 := by
  have hS0 : ∀ i, 0 ≤ S2 i := by
    intro i
    fin_cases i
    · norm_num [S2]
    · norm_num [S2]
  have hS : ∑ i, S2 i = 1 := by norm_num [S2, Fin.sum_univ_two]
  exact sum_phaseVolume_eq zero_le_one (by norm_num) hS0 hS

-- The factored total inventory theorem itself.
example : ∑ i, poreInventory 1 8 S2 rho2 i = 1 * 8 * ∑ i, S2 i * rho2 i := by
  exact sum_poreInventory 1 8 S2 rho2

-- Each admissible saturation is at most one, and each phase volume lies
-- in the pore volume.
example : S2 0 ≤ 1 ∧ S2 1 ≤ 1 := by
  have hS0 : ∀ i, 0 ≤ S2 i := by
    intro i
    fin_cases i
    · norm_num [S2]
    · norm_num [S2]
  have hS : ∑ i, S2 i = 1 := by norm_num [S2, Fin.sum_univ_two]
  exact ⟨saturation_le_one hS0 hS 0, saturation_le_one hS0 hS 1⟩

example : phaseVolume 1 8 S2 0 ≤ poreVolume 1 8 ∧
    0 ≤ phaseVolume 1 8 S2 0 := by
  have hS0 : ∀ i, 0 ≤ S2 i := by
    intro i
    fin_cases i
    · norm_num [S2]
    · norm_num [S2]
  have hS : ∑ i, S2 i = 1 := by norm_num [S2, Fin.sum_univ_two]
  exact ⟨phaseVolume_le_poreVolume zero_le_one (by norm_num) hS0 hS 0,
    phaseVolume_nonneg zero_le_one (by norm_num) hS0 0⟩

-- The velocity rewrite lemmas themselves.
example : (2 : ℝ) * superficialFlux (2 * 3) 2 = 2 * 3 := by
  exact volumetricFlow_eq 3 2 (by norm_num)

example : EarthScience.poreVelocity 3 (1 / 2) * (1 / 2) = 3 := by
  exact EarthScience.poreVelocity_mul (by norm_num)

-- Signed weights summing to one are not saturations: (-1, 2) sums to one
-- but its first phase volume is negative, so the admissibility hypotheses
-- cannot be dropped from the partition statement.
example : (∑ i, (![-1, 2] : Fin 2 → ℝ) i) = 1 ∧
    phaseVolume 1 1 (![-1, 2] : Fin 2 → ℝ) 0 = -1 := by
  constructor
  · norm_num [Fin.sum_univ_two]
  · unfold phaseVolume
    norm_num

-- Zero denominators are totalized values outside the physical domain, and
-- the velocity rewrite fails there without its hypothesis.
example : EarthScience.poreVelocity 3 0 = 0 ∧
    ¬ (EarthScience.poreVelocity 3 0 * 0 = 3) := by
  have h0 : EarthScience.poreVelocity 3 0 = 0 := by
    simp [EarthScience.poreVelocity]
  exact ⟨h0, by rw [h0]; norm_num⟩

example : superficialFlux 3 0 = 0 := by
  simp [superficialFlux]

end Engineering.Resource.PorousStorage.Tests
