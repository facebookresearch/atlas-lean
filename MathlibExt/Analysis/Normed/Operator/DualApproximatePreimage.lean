/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.Normed.Operator.DualLowerBound

/-!
# Controlled approximate preimages from a dual lower bound

For a bounded complex-linear map `B : E → F` between normed spaces, assume `‖G‖≤‖G∘B‖` for every
continuous `G ∈ F*`. Every `y ∈ F` then has an approximate preimage `x ∈ E` with `‖Bx-y‖≤‖y‖/2`
and `‖x‖≤2‖y‖`.

Completeness of the spaces is not required. For `y=0` the bound permits the zero preimage. An
exact preimage or surjectivity is not asserted.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Metric Set

namespace ContinuousLinearMap

noncomputable section

universe u v

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {F : Type v} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **Approximate preimage with fixed error and norm constants.** Let `E,F` be complex normed
spaces, with no completeness assumption, and `B : E →L[ℂ] F`. Assume `‖G‖≤‖G∘B‖` for every
continuous complex-linear functional `G ∈ F*`. for every `y ∈ F`, there exists `x ∈ E`
with `dist(Bx,y)≤(1/2)*‖y‖` and `‖x‖≤2*‖y‖`, including `y=0`. -/
theorem exists_controlled_approx_preimage_of_dual_lower_bound (B : E →L[ℂ] F)
    (hdual : ∀ G : StrongDual ℂ F, ‖G‖ ≤ ‖G.comp B‖) (y : F) :
    ∃ x : E, dist (B x) y ≤ (1 / 2 : ℝ) * ‖y‖ ∧ ‖x‖ ≤ 2 * ‖y‖ := by
  by_cases hy : y = 0
  · refine ⟨0, ?_, ?_⟩ <;> simp only [hy, map_zero, dist_self, norm_zero, mul_zero, le_refl]
  · let : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ ℂ E
    let : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ ℂ F
    let t : ℝ := 2 * ‖y‖
    have ht : 0 < t := mul_pos (by norm_num) (norm_pos_iff.mpr hy)
    let z : F := t⁻¹ • y
    have hz : ‖z‖ ≤ (1 / 2 : ℝ) := by
      change ‖t⁻¹ • y‖ ≤ (1 / 2 : ℝ)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
      dsimp only [t]
      field_simp
      ring_nf
      exact le_rfl
    have hclosure := B.halfBall_subset_closure_image_unitBall_of_dual_lower_bound hdual
      (mem_closedBall_zero_iff.mpr hz)
    obtain ⟨v, ⟨w, hw, rfl⟩, hv⟩ := Metric.mem_closure_iff.mp hclosure (1 / 4) (by norm_num)
    have hyz : t • z = y := by
      change t • (t⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    refine ⟨t • w, ?_, ?_⟩
    · have hdist : dist (B (t • w)) y = t * dist (B w) z := by
        rw [B.map_smul_of_tower, ← hyz, dist_eq_norm, ← smul_sub,
          norm_smul, Real.norm_eq_abs, abs_of_pos ht, dist_eq_norm]
      rw [hdist]
      have hsmall : dist (B w) z < (1 / 4 : ℝ) := by
        simpa only [dist_comm] using hv
      have h := mul_le_mul_of_nonneg_left hsmall.le ht.le
      dsimp only [t] at h ⊢
      nlinarith
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
      have hwNorm : ‖w‖ ≤ 1 := mem_closedBall_zero_iff.mp hw
      exact (mul_le_mul_of_nonneg_left hwNorm ht.le).trans_eq (mul_one t)

end

end ContinuousLinearMap
