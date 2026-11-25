/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedSobolevCritical
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Tactic.NormNum

open MeasureTheory
open scoped ENNReal

namespace MathlibExtTest.Analysis.FunctionalAnalysis.AnnulusWeightedSobolevCritical

open MathlibExt.Analysis.FunctionalAnalysis.AnnulusWeightedSobolevCriticalWanted

example {x : R2} (hx : ‖x‖ = 1) : phi x = 0 := by
  simp [phi, hx]

example {x : R2} (hx : ‖x‖ = 2) : phi x = 1 := by
  norm_num [phi, hx]

-- A constant function makes the gradient term vanish and uses the outer-annulus term.
private theorem const_one_bound {p : ℝ} (hp₁ : 1 ≤ p) (hp₂ : p < 2) :
    ∃ C : ℝ, 0 < C ∧
      eLpNorm phi (ENNReal.ofReal (pStar p)) (volume.restrict Omega1) ≤
        ENNReal.ofReal C * eLpNorm (fun _ : R2 => (1 : ℝ)) (ENNReal.ofReal p)
          (volume.restrict Omega2) := by
  have : IsFiniteMeasure (volume.restrict Omega2) := by
    constructor
    rw [Measure.restrict_apply_univ]
    exact (measure_mono Set.sdiff_subset).trans_lt (measure_ball_lt_top (μ := volume))
  obtain ⟨C, hC, h⟩ := exists_eLpNorm_phi_mul_le_weighted_grad_add_outer_annulus p hp₁ hp₂
  refine ⟨C, hC, ?_⟩
  have hp : MemLp (fun _ : R2 => (1 : ℝ)) (ENNReal.ofReal p) (volume.restrict Omega2) :=
    memLp_const 1
  simpa using h (fun _ => 1) contDiffOn_const (by simp) hp.eLpNorm_lt_top.ne

example : ∃ C : ℝ, 0 < C ∧
    eLpNorm phi 2 (volume.restrict Omega1) ≤
      ENNReal.ofReal C * eLpNorm (fun _ : R2 => (1 : ℝ)) 1 (volume.restrict Omega2) := by
  simpa [show pStar 1 = 2 by norm_num [pStar]] using
    const_one_bound (p := 1) le_rfl (by norm_num)

example : ∃ C : ℝ, 0 < C ∧
    eLpNorm phi 6 (volume.restrict Omega1) ≤
      ENNReal.ofReal C * eLpNorm (fun _ : R2 => (1 : ℝ)) (ENNReal.ofReal (3 / 2))
        (volume.restrict Omega2) := by
  simpa [show pStar (3 / 2) = 6 by norm_num [pStar]] using
    const_one_bound (p := 3 / 2) (by norm_num) (by norm_num)

end MathlibExtTest.Analysis.FunctionalAnalysis.AnnulusWeightedSobolevCritical
