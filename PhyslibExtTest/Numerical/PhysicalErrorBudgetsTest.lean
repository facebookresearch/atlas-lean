/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Numerical.PhysicalErrorBudgets
import Mathlib.Tactic.NormNum

/-!
# Tests for `PhyslibExt.Numerical.PhysicalErrorBudgets`

* a nonunit bar `EA = 2`, `L = 3`, `q = 4` on two uniform cells, keeping both the coordinate and
  the amplitude scaling;
* the same bar: the amplitude is nonzero, the reconstruction is fixed at both ends, and the
  physical error obeys the mesh estimates;
* the zero load, treated without the inverse amplitude map.
-/

@[expose] public section

namespace PhyslibExtTest.Numerical.PhysicalErrorBudgets

open _root_.PhysicalErrorBudgets

/-! ## A. A nonunit bar on two cells -/

-- Nonunit fixture `EA = 2`, `L = 3`, `q = 4`, keeping both the coordinate and the amplitude
-- scaling: `α = 9`, quarter-point error `9 / 16`, energy `9 / 2`, squared `L²` error `81 / 160`.
example :
    barAmplitude 2 3 4 = 9 ∧ physicalError twoCells 2 3 4 (3 / 4) = 9 / 16 ∧
      ∫ x in (0 : ℝ)..3, 2 * deriv (physicalError twoCells 2 3 4) x ^ 2 = 9 / 2 ∧
      ∫ x in (0 : ℝ)..3, physicalError twoCells 2 3 4 x ^ 2 = 81 / 160 := by
  have hα : barAmplitude 2 3 4 = 9 := by norm_num [barAmplitude]
  obtain ⟨h1, h2, h3⟩ := physicalError_twoCells (L := 3) (by norm_num) 2 4
  refine ⟨hα, ?_, ?_, ?_⟩
  · rw [h1, hα]
  · rw [h2, hα]
    norm_num
  · rw [h3, hα]
    norm_num

-- The amplitude of that bar is nonzero, so the normalization can be inverted.
example : barAmplitude 2 3 4 ≠ 0 :=
  (barAmplitude_ne_zero_iff (by norm_num) (by norm_num) 4).2 (by norm_num)

-- Its reconstruction is fixed at both ends of `[0, 3]`.
example : physicalP1 twoCells 2 3 4 0 = 0 ∧ physicalP1 twoCells 2 3 4 3 = 0 :=
  physicalP1_zero_and_length twoCells (by norm_num) 2 4

-- The energy and `L²` errors obey the physical mesh estimates.
example :
    ∫ x in (0 : ℝ)..3, 2 * deriv (physicalError twoCells 2 3 4) x ^ 2 ≤
        2 / 3 * barAmplitude 2 3 4 ^ 2 * (4 * (twoCells.mesh / Real.pi) ^ 2) ∧
      ∫ x in (0 : ℝ)..3, physicalError twoCells 2 3 4 x ^ 2 ≤
        3 * barAmplitude 2 3 4 ^ 2 * (4 * (twoCells.mesh / Real.pi) ^ 4) :=
  ⟨integral_energy_physicalError_le_mesh twoCells (by norm_num) (by norm_num) 4,
    integral_sq_physicalError_le_mesh twoCells (by norm_num) 2 4⟩

/-! ## B. Zero load -/

-- With `q = 0` the error vanishes everywhere, and the inverse amplitude map does not recover
-- the unit profile.
example :
    physicalError twoCells 2 3 0 (3 / 4) = 0 ∧
      (barAmplitude 2 3 0)⁻¹ * Elasticity.PrismaticMembers.axialDisplacement 2 3 0 (3 * (1 / 2)) ≠
        unitProfile (1 / 2) :=
  ⟨(zero_load twoCells 2 3).2.2.2 (3 / 4), zero_load_inverse_ne 2 3⟩

end PhyslibExtTest.Numerical.PhysicalErrorBudgets

end
