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

/-- Two-phase densities `(1, 2)`. -/
def rho2 : Fin 2 → ℝ := ![1, 2]

-- The sum identity itself, at porosity 1 and bulk volume 8: only the
-- saturations summing to one is needed.
example : ∑ i, phaseVolume 1 8 S2 i = poreVolume 1 8 := by
  have hS : ∑ i, S2 i = 1 := by norm_num [S2, Fin.sum_univ_two]
  exact sum_phaseVolume_eq hS

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

example : ∑ i, phaseVolume 1 1 (![-1, 2] : Fin 2 → ℝ) i =
    poreVolume 1 1 := by
  have hS : ∑ i, (![-1, 2] : Fin 2 → ℝ) i = 1 := by norm_num [Fin.sum_univ_two]
  exact sum_phaseVolume_eq hS

-- The documented numerical fixture evaluated: porosity 1/4 and bulk
-- volume 8 give pore volume 2, phase volumes 1/2 and 3/2, and total
-- inventory 7/2 at densities (1, 2).
example : phaseVolume (1 / 4) 8 S2 0 = 1 / 2 ∧
    phaseVolume (1 / 4) 8 S2 1 = 3 / 2 ∧
    (∑ i, poreInventory (1 / 4) 8 S2 rho2 i) = 7 / 2 := by
  constructor
  · norm_num [phaseVolume, S2]
  · constructor
    · norm_num [phaseVolume, S2]
    · norm_num [poreInventory, S2, rho2, Fin.sum_univ_two]

-- The velocity rewrite lemmas themselves.
example : (2 : ℝ) * superficialFlux (2 * 3) 2 = 2 * 3 := by
  exact volumetricFlow_eq_mul 3 2 (by norm_num)

example : EarthScience.poreVelocity 3 (1 / 2) * (1 / 2) = 3 := by
  exact EarthScience.poreVelocity_mul (by norm_num)

-- The imported conversion divides by the whole porosity, so it is not the
-- velocity of one phase: at porosity and saturation `1/2` a unit phase flux
-- gives `2`, while that phase fills only the bulk fraction `1/4` and so
-- moves at `1 / (1/4) = 4`.
example : EarthScience.poreVelocity 1 (1 / 2) = 2 ∧
    phaseVolume (1 / 2) 1 (![1 / 2, 1 / 2] : Fin 2 → ℝ) 0 = 1 / 4 ∧
    1 / phaseVolume (1 / 2) 1 (![1 / 2, 1 / 2] : Fin 2 → ℝ) 0 = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [EarthScience.poreVelocity, phaseVolume]

-- The general flux law serves any flow `Q`, which the special case for
-- flows written as `A * u` cannot match.
example (Q A : ℝ) (hA : A ≠ 0) : A * superficialFlux Q A = Q := by
  fail_if_success exact volumetricFlow_eq_mul _ A hA
  exact volumetricFlow_eq Q A hA

example : (2 : ℝ) * superficialFlux 3 2 = 3 := by
  exact volumetricFlow_eq 3 2 (by norm_num)

-- Signed weights summing to one still satisfy the algebraic sum
-- identity, but they are not saturations: the first phase volume is
-- negative, so the admissibility hypotheses cannot be dropped from the
-- nonnegativity and bound lemmas.
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

-- At zero area the totalized flux gives zero flow, so the flux law needs
-- `A ≠ 0`.
example : ¬ ((0 : ℝ) * superficialFlux 3 0 = 3) := by
  simp [superficialFlux]

end Engineering.Resource.PorousStorage.Tests
