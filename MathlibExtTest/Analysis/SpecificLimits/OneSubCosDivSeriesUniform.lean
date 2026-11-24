/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.OneSubCosDivSeriesUniform

/-! # Tests for uniform convergence of the cosine difference series -/

open MathlibExt.Analysis.SpecificLimits.OneSubCosDivSeriesUniformWanted

-- On a nonpositive interval the uniform limit vanishes at the right endpoint zero.
example : ∃ g : ℝ → ℝ, g 0 = 0 ∧
    TendstoUniformlyOn (fun (N : ℕ) (x : ℝ) => ∑ n ∈ Finset.range N, (1 - Real.cos (x / (n + 1))))
      g Filter.atTop (Set.Icc (-1) 0) := by
  obtain ⟨g, hg⟩ := tendstoUniformlyOn_sum_one_sub_cos_div _ (fun _ _ => rfl) (-1) 0 (by norm_num)
  refine ⟨g, ?_, hg⟩
  have hzero := hg.tendsto_at (show (0 : ℝ) ∈ Set.Icc (-1) 0 by constructor <;> norm_num)
  exact tendsto_nhds_unique (by simpa using hzero : Filter.Tendsto (fun _ : ℕ => (0 : ℝ))
    Filter.atTop (nhds (g 0))) tendsto_const_nhds
