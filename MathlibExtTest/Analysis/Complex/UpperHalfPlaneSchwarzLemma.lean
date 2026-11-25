/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Complex.UpperHalfPlaneSchwarzLemma
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # Tests for `MathlibExt.Analysis.Complex.UpperHalfPlaneSchwarzLemma` -/

namespace MathlibExtTest.UpperHalfPlaneSchwarzLemma

open Complex MathlibExt.Analysis.Complex.UpperHalfPlaneSchwarzLemmaWanted

/-- A point of the upper half-plane is closer to `I` than to `-I`. -/
private lemma norm_sub_I_lt_norm_add_I {z : ℂ} (hz : 0 < z.im) : ‖z - I‖ < ‖z + I‖ := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), Complex.sq_norm, Complex.sq_norm,
    normSq_apply, normSq_apply]
  simp only [sub_re, sub_im, add_re, add_im, I_re, I_im, sub_zero, add_zero]
  nlinarith

-- Test section: at `z = 2 I` the bound is `‖(2 I - I) / (2 I + I)‖ = 1 / 3`.
example (F : ℂ → ℂ) (hHolo : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hBound : ∀ z, 0 < z.im → ‖F z‖ ≤ 1) (hFi : F I = 0) :
    ‖F (2 * I)‖ ≤ 1 / 3 := by
  have h := norm_le_norm_cayley_of_upperHalfPlane_bounded_vanishing_at_I F hHolo hBound hFi
    (2 * I) (by simp)
  have hq : (2 * I - I) / (2 * I + I) = 1 / 3 := by
    field_simp
    ring
  rwa [hq, norm_div, norm_one, Complex.norm_ofNat] at h

-- Test section: the bound is strict, so such an `F` never reaches the unit circle on the
-- upper half-plane.
example (F : ℂ → ℂ) (hHolo : DifferentiableOn ℂ F {z : ℂ | 0 < z.im})
    (hBound : ∀ z, 0 < z.im → ‖F z‖ ≤ 1) (hFi : F I = 0) {z : ℂ} (hz : 0 < z.im) :
    ‖F z‖ < 1 := by
  have hlt := norm_sub_I_lt_norm_add_I hz
  refine (norm_le_norm_cayley_of_upperHalfPlane_bounded_vanishing_at_I F hHolo hBound hFi
    z hz).trans_lt ?_
  rw [norm_div, div_lt_one ((norm_nonneg _).trans_lt hlt)]
  exact hlt

-- Test section: the Cayley map `z ↦ (z - I) / (z + I)` satisfies every hypothesis and attains
-- the bound at each point, so the hypotheses are jointly satisfiable and the bound is sharp.
example : DifferentiableOn ℂ (fun z : ℂ => (z - I) / (z + I)) {z : ℂ | 0 < z.im} ∧
    (∀ z : ℂ, 0 < z.im → ‖(z - I) / (z + I)‖ ≤ 1) ∧ (I - I) / (I + I) = 0 := by
  have hne {z : ℂ} (hz : 0 < z.im) : z + I ≠ 0 :=
    norm_pos_iff.mp ((norm_nonneg _).trans_lt (norm_sub_I_lt_norm_add_I hz))
  refine ⟨fun z hz => ?_, fun z hz => ?_, by simp⟩
  · exact ((differentiableAt_id.sub_const I).div (differentiableAt_id.add_const I)
      (hne hz)).differentiableWithinAt
  · rw [norm_div, div_le_one (norm_pos_iff.mpr (hne hz))]
    exact (norm_sub_I_lt_norm_add_I hz).le

end MathlibExtTest.UpperHalfPlaneSchwarzLemma
