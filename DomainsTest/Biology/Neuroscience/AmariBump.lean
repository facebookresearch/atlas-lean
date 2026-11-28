/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Neuroscience.AmariBump
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Tests for Amari's bump-width equation

With no coupling, input `1` and threshold `0`, the solution `1 - exp (-t) * x²` has
interfaces at `±exp (t/2)`. At `t = 0`, the width has derivative `1`.
-/

open MeasureTheory Set WantedExt.Biology.Neuroscience.AmariBumpWanted

private noncomputable def radius (t : ℝ) : ℝ := Real.exp (t / 2)

private noncomputable def profile (x t : ℝ) : ℝ := 1 - Real.exp (-t) * x ^ 2

private theorem radius_pos (t : ℝ) : 0 < radius t := Real.exp_pos _

private theorem radius_hasDerivAt (t : ℝ) : HasDerivAt radius (radius t / 2) t := by
  change HasDerivAt (fun τ ↦ Real.exp (τ / 2)) (Real.exp (t / 2) / 2) t
  simpa only [Function.comp_def, id_eq, div_eq_mul_inv, one_mul] using
    (Real.hasDerivAt_exp (t / 2)).comp t ((hasDerivAt_id t).div_const 2)

private theorem excited (t : ℝ) : {x | 0 < profile x t} = Ioo (-radius t) (radius t) := by
  have hsquare : Real.exp (-t) * radius t ^ 2 = 1 := by
    rw [radius, pow_two, ← Real.exp_add, ← Real.exp_add, show -t + (t / 2 + t / 2) = 0 by ring,
      Real.exp_zero]
  ext x
  rw [mem_ofPred_eq, profile, sub_pos, ← hsquare, mul_lt_mul_iff_right₀ (Real.exp_pos (-t)),
    ← sq_abs x, sq_lt_sq₀ (abs_nonneg x) (radius_pos t).le, abs_lt, mem_Ioo]

private theorem space_deriv (x t : ℝ) :
    deriv (fun y ↦ profile y t) x = -Real.exp (-t) * (2 * x) := by
  simp [profile, neg_mul]

private theorem time_deriv (x t : ℝ) :
    HasDerivAt (profile x) (-profile x t + fieldInput (fun _ ↦ 0) 0 1 (fun y ↦ profile y t) x)
      t := by
  rw [fieldInput_zero_kernel]
  have hd : HasDerivAt (profile x) (-(Real.exp (-t) * -1 * x ^ 2)) t :=
    (((Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg).mul_const (x ^ 2)).const_sub 1
  convert hd using 2
  dsimp [profile]
  ring

private theorem left_positive (t : ℝ) : 0 < deriv (fun x ↦ profile x t) (-radius t) := by
  rw [space_deriv]
  exact mul_pos_of_neg_of_neg (neg_neg_of_pos (Real.exp_pos _))
    (mul_neg_of_pos_of_neg (by norm_num) (neg_neg_of_pos (radius_pos t)))

private theorem right_negative (t : ℝ) : deriv (fun x ↦ profile x t) (radius t) < 0 := by
  rw [space_deriv]
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (Real.exp_pos _))
    (mul_pos (by norm_num) (radius_pos t))

-- Independently differentiate the explicit width by differentiating its endpoints.
example : HasDerivAt (fun t ↦ radius t - -radius t) 1 0 := by
  convert (radius_hasDerivAt 0).sub (radius_hasDerivAt 0).neg using 2
  norm_num [radius]

-- Independently evaluate the interface formula: the endpoint slopes at `0` are `2` and `-2`.
private theorem interface_rhs_at_zero :
    (kernelPrimitive (fun _ ↦ 0) (radius 0 - -radius 0) + 1 - 0) *
      (1 / deriv (fun x ↦ profile x 0) (-radius 0) +
        1 / -deriv (fun x ↦ profile x 0) (radius 0)) = 1 := by
  norm_num [space_deriv, radius]

-- Apply the public theorem to the same solution, with every hypothesis checked above or here.
example : HasDerivAt (fun t ↦ radius t - -radius t) 1 0 := by
  have hw : IsKernel (fun _ ↦ 0) :=
    IsKernel.mk continuous_const (fun _ ↦ rfl) (integrable_fun_zero ℝ ℝ volume)
  have hu : ContDiff ℝ 1 (fun p : ℝ × ℝ ↦ profile p.1 p.2) :=
    contDiff_const.sub ((Real.contDiff_exp.comp contDiff_snd.neg).mul (contDiff_fst.pow 2))
  have hd (t : ℝ) := (radius_hasDerivAt t).differentiableAt
  have h := hasDerivAt_width hw 0 1 profile hu time_deriv (fun t ↦ -radius t) radius
    (fun t ↦ (hd t).neg) hd (fun t ↦ neg_lt_self (radius_pos t)) excited
    left_positive right_negative 0
  simpa only [interface_rhs_at_zero] using h
