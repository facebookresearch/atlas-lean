/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import MathlibExt.Analysis.Complex.Residue

set_option autoImplicit false

open Complex Metric Set
open scoped Real

-- A simple pole with a vector coefficient: the residue of `(z - a)⁻¹ • v` at `a` is `v`.
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (a : ℂ) (v : E) :
    residue (fun z => (z - a)⁻¹ • v) a = v := by
  rw [residue_eq_circleIntegral (Ω := univ) ?_ one_pos (subset_univ _),
    circleIntegral.integral_smul_const,
    circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self one_pos), smul_smul,
    inv_mul_cancel₀ two_pi_I_ne_zero, one_smul]
  exact ((differentiableOn_id.sub_const a).fun_inv fun z hz => sub_ne_zero.2 hz.2).smul_const v

-- The closed-disc reading of "circle contained in `Ω`" matters: `(z - 2)⁻¹` is holomorphic on
-- `Ω = ℂ \ {2}` and the circle `|z| = 3` lies in `Ω`, but the normalized integral over it is `1`,
-- while the residue at `0` is `0`.
example :
    residue (fun z : ℂ => (z - 2)⁻¹) 0 = 0 ∧ sphere (0 : ℂ) 3 ⊆ {2}ᶜ ∧
      (2 * π * I)⁻¹ • ∮ z in C(0, 3), (z - 2)⁻¹ = 1 := by
  have hf : DifferentiableOn ℂ (fun z : ℂ => (z - 2)⁻¹) {2}ᶜ :=
    (differentiableOn_id.sub_const 2).fun_inv fun z hz => sub_ne_zero.2 hz
  have hdisc : closedBall (0 : ℂ) 1 ⊆ {2}ᶜ := by
    rintro z hz rfl
    norm_num [mem_closedBall_zero_iff] at hz
  refine ⟨?_, ?_, ?_⟩
  · rw [residue_eq_circleIntegral (hf.mono sdiff_subset) one_pos hdisc,
      (hf.diffContOnCl_ball hdisc).circleIntegral_eq_zero zero_le_one, smul_zero]
  · rintro z hz rfl
    norm_num [mem_sphere_zero_iff_norm] at hz
  · rw [circleIntegral.integral_sub_inv_of_mem_ball (by norm_num [mem_ball_zero_iff]),
      smul_eq_mul, inv_mul_cancel₀ two_pi_I_ne_zero]

#print axioms Complex.residue_eq_circleIntegral
