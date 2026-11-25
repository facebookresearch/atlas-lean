/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.FunctionalAnalysis.ScottishBook64

open Set MathlibExt.Analysis.FunctionalAnalysis.ScottishBook64Wanted

-- Put the right interval first, so the separating functional must reverse the endpoint order.
example : ∃ (F : ℝ →L[ℝ] ℝ) (c : ℝ), F ≠ 0 ∧ F 2 ≤ c ∧ c ≤ F 1 := by
  obtain ⟨F, c, hF, hA, hB⟩ := convexBodiesSeparatedByHyperplane ℝ (Icc 2 3) (Icc 0 1)
    (convex_Icc ..) isClosed_Icc (by rw [interior_Icc]; exact nonempty_Ioo.mpr (by norm_num))
    ⟨3, fun a ha => by rw [Real.norm_of_nonneg (by linarith [ha.1])]; exact ha.2⟩
    (convex_Icc ..) isClosed_Icc (by rw [interior_Icc]; exact nonempty_Ioo.mpr (by norm_num))
    ⟨1, fun b hb => by simpa [Real.norm_of_nonneg hb.1] using hb.2⟩
    ⟨1, zero_lt_one, fun a ha b hb => by
      rw [Real.dist_eq]
      exact (show 1 ≤ a - b by linarith [ha.1, hb.2]).trans (le_abs_self _)⟩
  exact ⟨F, c, hF, hA 2 (left_mem_Icc.mpr (by norm_num)), hB 1 (right_mem_Icc.mpr zero_le_one)⟩
