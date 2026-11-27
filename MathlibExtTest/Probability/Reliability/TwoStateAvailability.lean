/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Reliability.TwoStateAvailability
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Examples of finite-time availability and its limits -/

open Filter Matrix ProbabilityTheory Topology

-- Unequal rates and a nonstationary initial law exercise both coefficients of the formula.
example (t : ℝ) :
    (![(1 / 4 : ℝ), 3 / 4] ᵥ* ctmcTransition !![-(1 : ℝ), 1; 3, -3] t) 0 =
      3 / 4 - (1 / 2) * Real.exp (-(4 * t)) := by
  have h := two_state_component_availability 1 3 (1 / 4)
    (by norm_num) (by norm_num) (by constructor <;> norm_num)
  have hform := (h.2.2.2.1 (by norm_num)).1 t
  norm_num at hform ⊢
  convert hform using 1

-- When both rates vanish, a mixed initial distribution is unchanged.
example :
    (![(1 / 3 : ℝ), 1 - 1 / 3] ᵥ* ctmcTransition (0 : Matrix (Fin 2) (Fin 2) ℝ) 2) 0 =
      1 / 3 := by
  have h := two_state_component_availability 0 0 (1 / 3)
    (by norm_num) (by norm_num) (by constructor <;> norm_num)
  have hzero := h.2.2.2.2.1 rfl rfl 2
  have hQ : (!![-(0 : ℝ), 0; 0, -0] : Matrix (Fin 2) (Fin 2) ℝ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  simpa only [hQ] using hzero

-- With no failures, an initially up component stays up even when the repair rate is positive.
example (t : ℝ) : ( ![(1 : ℝ), 0] ᵥ* ctmcTransition !![0, 0; 2, -(2 : ℝ)] t) 0 = 1 := by
  have h := two_state_component_availability 0 2 1
    (by norm_num) (by norm_num) (by constructor <;> norm_num)
  simpa only [neg_zero, sub_self] using h.2.2.2.2.2.1 rfl rfl t

-- With no repairs, positive failure rate gives zero limiting availability.
example : Tendsto (fun t => (![(1 : ℝ), 0] ᵥ* ctmcTransition !![-(2 : ℝ), 2; 0, 0] t) 0)
    atTop (𝓝 0) := by
  have h := two_state_component_availability 2 0 1
    (by norm_num) (by norm_num) (by constructor <;> norm_num)
  simpa only [neg_zero, sub_self] using h.2.2.2.2.2.2 rfl (by norm_num)
