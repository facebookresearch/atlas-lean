/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.WeightedLadyzhenskayaPlane
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory
open scoped ContDiff ENNReal
open MathlibExt.Analysis.FunctionalAnalysis.WeightedLadyzhenskayaPlaneWanted

/-- The constant unit weight recovers the unweighted inhomogeneous estimate. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ u : EuclideanSpace ℝ (Fin 2) → ℝ,
    ContDiff ℝ ∞ u → HasCompactSupport u →
      ∫ x, u x ^ (4 : ℕ) ≤ C * (eLpNorm u 2 volume).toReal ^ (2 : ℕ) *
        ∫ x, (‖fderiv ℝ u x‖ ^ (2 : ℕ) + |u x| ^ (2 : ℕ)) := by
  obtain ⟨C, hC, h⟩ := exists_const_integral_pow_four_mul_weight_le
  refine ⟨C, hC, fun u hu huK ↦ ?_⟩
  have hzero : eLpNorm (fun x : EuclideanSpace ℝ (Fin 2) =>
      ‖fderiv ℝ (fun _ : EuclideanSpace ℝ (Fin 2) => (1 : ℝ)) x‖ / (1 : ℝ)) ⊤ volume ≤ 1 := by
    simp
  simpa only [mul_one] using h (fun _ ↦ 1) (fun _ ↦ zero_lt_one) contDiff_const hzero u hu huK
