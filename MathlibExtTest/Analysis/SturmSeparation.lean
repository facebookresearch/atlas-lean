/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Analysis.SturmSeparation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Tests for Sturm separation -/

open Real Set MathlibExt.Analysis.SturmSeparationWanted.Analysis.ODE

-- On the open half-line above -π, the Wronskian witness at 2π lies beyond both endpoint zeros.
example : ∃! c, c ∈ Ioo (0 : ℝ) π ∧ cos c = 0 := by
  refine sturm_separation (fun _ => 0) (fun _ => 1) sin cos 0 π pi_pos (Ioi (-π))
    isOpen_Ioi isPreconnected_Ioi (fun x hx => (neg_lt_zero.mpr pi_pos).trans_le hx.1)
    continuousOn_const continuousOn_const ?_ ?_ ?_ ?_ ?_ sin_zero sin_pi
    (fun x hx => (sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne')
  · intro x _
    simpa only [Real.deriv_sin] using hasDerivAt_sin x
  · intro x _
    simpa [Real.deriv_sin] using hasDerivAt_cos x
  · intro x _
    simpa only [Real.deriv_cos] using hasDerivAt_cos x
  · intro x _
    simpa [Real.deriv_cos'] using (hasDerivAt_sin x).fun_neg
  · exact ⟨2 * π, (neg_lt_zero.mpr pi_pos).trans two_pi_pos, by simp [Real.deriv_sin]⟩
