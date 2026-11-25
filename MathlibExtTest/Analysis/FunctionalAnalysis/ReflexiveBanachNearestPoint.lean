/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ReflexiveBanachNearestPoint
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Set Metric NormedSpace MathlibExt.Analysis.FunctionalAnalysis.ReflexiveBanachNearestPointWanted

private theorem complex_bidually_surjective : Function.Surjective (inclusionInDoubleDual ℂ ℂ) := by
  intro Φ
  let e : ℂ →L[ℂ] ℂ := ContinuousLinearMap.id ℂ ℂ
  refine ⟨Φ e, ?_⟩
  apply ContinuousLinearMap.ext
  intro f
  rw [dual_def]
  have hf : f = f 1 • e := by
    apply ContinuousLinearMap.ext
    intro z
    simpa [e, smul_eq_mul, mul_comm] using f.map_smul z (1 : ℂ)
  rw [hf, map_smul]
  simp [e, smul_eq_mul]

-- From the real point `2` in `ℂ`, the distance to the closed unit disc is `1`.
example : ∃ y ∈ closedBall (0 : ℂ) 1, ‖(2 : ℂ) - y‖ = 1 := by
  let C := closedBall (0 : ℂ) 1
  have h1 : (1 : ℂ) ∈ C := by simp [C]
  obtain ⟨y, hy, hdist⟩ := exists_norm_sub_eq_iInf_of_reflexive_of_convex_of_isClosed ℂ complex_bidually_surjective C
    isClosed_closedBall (convex_closedBall _ _) ⟨1, h1⟩ (2 : ℂ)
  refine ⟨y, hy, le_antisymm ?_ ?_⟩
  · rw [hdist]
    have hB : BddBelow (Set.range (fun z : C => ‖(2 : ℂ) - (z : ℂ)‖)) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨z, rfl⟩
      exact norm_nonneg _
    have h := ciInf_le hB (⟨1, h1⟩ : C)
    norm_num at h
    exact h
  · have hyn : ‖y‖ ≤ 1 := by simpa [C, mem_closedBall] using hy
    have ht := norm_add_le ((2 : ℂ) - y) y
    rw [sub_add_cancel] at ht
    norm_num at ht
    linarith
