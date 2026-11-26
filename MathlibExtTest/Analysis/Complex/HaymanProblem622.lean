/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Add
import MathlibExt.Analysis.Complex.HaymanProblem622

open Metric MathlibExt.Analysis.HaymanProblem622Wanted

namespace MathlibExtTest.Analysis.Complex.HaymanProblem622

private def P (z : ℂ) : ℂ := 1 + z

-- This Carathéodory function satisfies the criterion throughout the common open disc,
-- including its center. The criterion fails at -4/5, which bounds the radius.
example : ∃ r : ℝ, 0 < r ∧ r ≤ 4 / 5 ∧ ∀ z ∈ ball (0 : ℂ) r,
    0 < ((P z + 1) / (2 : ℂ) + z * deriv P z / (P z + 1)).re := by
  obtain ⟨r, hr, _, ⟨_, hcar⟩, _⟩ := conjecture_holds
  have hPd (z : ℂ) : HasDerivAt P 1 z := (hasDerivAt_id z).const_add 1
  have hP : Differentiable ℂ P := fun z ↦ (hPd z).differentiableAt
  have hP₀ : P 0 = 1 := by simp [P]
  have hRe (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) : 0 < (P z).re := by
    have h := mem_ball_zero_iff.mp hz
    simp [P]
    linarith [Complex.abs_re_le_norm z, neg_le_abs z.re]
  have hpos (z : ℂ) (hz : z ∈ ball (0 : ℂ) r) :
      0 < ((P z + 1) / (2 : ℂ) + z * deriv P z / (P z + 1)).re :=
    hcar P hP.differentiableOn hP₀ hRe ‖z‖ (norm_nonneg _) (mem_ball_zero_iff.mp hz) z
      (mem_sphere_zero_iff_norm.mpr rfl)
  refine ⟨r, hr, le_of_not_gt ?_, hpos⟩
  intro hlarge
  let z : ℂ := (-(4 / 5 : ℝ) : ℂ)
  have hz : z ∈ ball (0 : ℂ) r := by
    apply mem_ball_zero_iff.mpr
    simpa [z, Complex.norm_real, Real.norm_eq_abs] using hlarge
  have h := hpos z hz
  rw [(hPd z).deriv] at h
  norm_num [P, z, Complex.div_re, Complex.normSq_apply] at h

end MathlibExtTest.Analysis.Complex.HaymanProblem622
