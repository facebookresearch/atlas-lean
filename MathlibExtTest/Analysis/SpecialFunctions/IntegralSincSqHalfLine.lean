/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.IntegralSincSqHalfLine
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-! # Tests for the squared sinc integral -/

open MathlibExt.Analysis.SpecialFunctions.IntegralSincSqHalfLineWanted MeasureTheory Real Set

-- The continuous extension takes the value one at zero, and gives the same integral on [0, ∞).
example : ∫ x in Ici (0 : ℝ), sinc x ^ 2 = π / 2 := by
  rw [integral_Ici_eq_integral_Ioi, ← integral_sin_div_sq_Ioi_eq_pi_div_two]
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [sinc_of_ne_zero hx.out.ne']
