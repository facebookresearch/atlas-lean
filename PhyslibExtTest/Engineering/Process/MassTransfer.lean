/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.MassTransfer

import Mathlib.Tactic.NormNum

/-!
# Tests for interphase mass transfer

Boundary checks for `PhyslibExt.Engineering.Process.MassTransfer` with
`H = 2`, `p = 3`, and unit coefficients, exercised through the public
lemmas: absorption below equilibrium, desorption above it, zero rate at
equilibrium, surface-to-volumetric scaling, and the pressure and
volatility forms.
-/

namespace Engineering.Process.MassTransfer.Tests

open Engineering.Process.MassTransfer

-- H = 2, p = 3, c = 1, k = a = 1: driving force 5, absorption, through
-- the apply lemma and the positivity lemma.
example : volumetricRate 1 1 2 3 1 = 5 := by
  rw [volumetricRate_apply]
  norm_num

example : 0 < volumetricRate 1 1 2 3 1 := by
  exact volumetricRate_pos (by norm_num) (by norm_num) (by norm_num)

-- c = 7: desorption, through the negativity lemma.
example : volumetricRate 1 1 2 3 7 < 0 := by
  exact volumetricRate_neg (by norm_num) (by norm_num) (by norm_num)

-- Zero driving force at c = H * p = 6, through the equilibrium lemma in
-- both directions.
example : volumetricRate 1 1 2 3 6 = 0 := by
  have h1 : (0 : ℝ) < 1 := by norm_num
  have h2 : (6 : ℝ) = 2 * 3 := by norm_num
  exact (volumetricRate_eq_zero_iff h1 h1).mpr h2

example : volumetricRate 1 1 2 3 1 ≠ 0 := by
  intro hcon
  have h1 : (0 : ℝ) < 1 := by norm_num
  have hc := (volumetricRate_eq_zero_iff h1 h1).mp hcon
  norm_num at hc

-- Surface flux and its scaling to the volumetric rate at a = 2.
example : surfaceFlux 1 2 3 1 = 5 ∧ volumetricRate 1 2 2 3 1 = 10 := by
  constructor
  · unfold surfaceFlux
    norm_num
  · rw [volumetricRate_eq]
    unfold surfaceFlux
    norm_num

-- Pressure form, through the pressure-doubling lemma: at doubled
-- pressure the driving force is 2 * (2 * 3) - 1 = 11.
example : volumetricRate 1 1 2 (2 * 3) 1 = 11 := by
  rw [volumetricRate_pressure_double]
  norm_num

-- Volatility form agrees numerically: H = 1 / (1/2) = 2, through the
-- volatility lemma.
example : volumetricRate 1 1 (1 / (1 / 2 : ℝ)) 3 1 = 5 := by
  have hHpc : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hH : (1 / (1 / 2 : ℝ)) = 1 / (1 / 2 : ℝ) := rfl
  rw [volumetricRate_volatility_form hHpc hH]
  norm_num

end Engineering.Process.MassTransfer.Tests
