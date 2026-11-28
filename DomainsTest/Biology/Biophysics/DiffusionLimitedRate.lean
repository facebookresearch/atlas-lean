/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.Biophysics.DiffusionLimitedRate
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Checks for Smoluchowski's steady radial current -/

open Filter Set Topology WantedExt.Biology.Biophysics.DiffusionLimitedRateWanted

private noncomputable def profile (a r : ℝ) : ℝ := a * (1 - 3 * r⁻¹)

private theorem profile_boundary (a : ℝ) : profile a 3 = 0 := by
  norm_num [profile]

private theorem profile_limit (a : ℝ) : Tendsto (profile a) atTop (𝓝 a) := by
  change Tendsto (fun r : ℝ => a * (1 - 3 * r⁻¹)) atTop (𝓝 a)
  have h : Tendsto (fun r : ℝ => 1 - 3 * r⁻¹) atTop (𝓝 (1 - 3 * 0)) :=
    tendsto_const_nhds.sub (tendsto_inv_atTop_zero.const_mul 3)
  simpa only [mul_zero, sub_zero, mul_one] using h.const_mul a

-- Compute the current directly for D = 2 and R = 3, including the one-sided derivative at R.
private theorem profile_current (a r : ℝ) (hr : 3 ≤ r) :
    4 * Real.pi * r ^ 2 * 2 * derivWithin (profile a) (Ici 3) r = 24 * Real.pi * a := by
  have hr0 : r ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hr)
  have hd : HasDerivWithinAt (profile a) (a * (3 * (r ^ 2)⁻¹)) (Ici 3) r := by
    change HasDerivWithinAt (fun y : ℝ => a * (1 - 3 * y⁻¹)) (a * (3 * (r ^ 2)⁻¹)) (Ici 3) r
    simpa only [mul_neg, neg_neg] using
      (((hasDerivWithinAt_inv hr0 (Ici 3)).const_mul 3).const_sub 1).const_mul a
  rw [hd.derivWithin (uniqueDiffOn_Ici 3 r hr)]
  field_simp [hr0]
  ring

example : profile 1 3 = 0 ∧ Tendsto (profile 1) atTop (𝓝 1) ∧
    ∀ r : ℝ, 3 ≤ r →
      4 * Real.pi * r ^ 2 * 2 * derivWithin (profile 1) (Ici 3) r = 24 * Real.pi := by
  refine ⟨profile_boundary 1, profile_limit 1, fun r hr => ?_⟩
  simpa using profile_current 1 r hr

example : profile 0 3 = 0 ∧ Tendsto (profile 0) atTop (𝓝 0) ∧
    ∀ r : ℝ, 3 ≤ r →
      4 * Real.pi * r ^ 2 * 2 * derivWithin (profile 0) (Ici 3) r = 0 := by
  refine ⟨profile_boundary 0, profile_limit 0, fun r hr => ?_⟩
  simpa using profile_current 0 r hr

example : profile (-1) 3 = 0 ∧ Tendsto (profile (-1)) atTop (𝓝 (-1)) ∧
    ∀ r : ℝ, 3 ≤ r →
      4 * Real.pi * r ^ 2 * 2 * derivWithin (profile (-1)) (Ici 3) r = -(24 * Real.pi) := by
  refine ⟨profile_boundary (-1), profile_limit (-1), fun r hr => ?_⟩
  simpa using profile_current (-1) r hr

-- A client can use the public theorem with a steady-profile assumption at negative bulk value.
example (J : ℝ) (hn : IsSteadyProfile 2 1 3 (fun _ => 0) (profile (-1)) J) :
    J = -(24 * Real.pi) := by
  calc
    J = 4 * Real.pi * 2 * 3 * (-1) :=
      current_eq_smoluchowski 2 1 3 (by norm_num) (by norm_num) (by norm_num) (-1)
        (profile (-1)) J hn (profile_boundary _) (profile_limit _)
    _ = -(24 * Real.pi) := by ring
