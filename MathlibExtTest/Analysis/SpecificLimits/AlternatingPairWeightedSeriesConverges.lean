/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.AlternatingPairWeightedSeriesConverges

open Filter Topology

namespace MathlibExt.Analysis.SpecificLimits.AlternatingPairWeightedSeriesConvergesWanted

private def direction (k : ℕ) : ℝ × ℝ := if Even k then (0, 1) else (1, 0)

private noncomputable def partialSum (n : ℕ) : ℝ × ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (1 / (k : ℝ) ^ 2) • direction k

example : ∃ L : ℝ × ℝ, Tendsto partialSum atTop (𝓝 L) :=
  exists_tendsto_sum_inv_sq_smul_alternating_pair 0 1 direction partialSum
    (fun _ ↦ rfl) (fun _ ↦ rfl)

example : partialSum 0 = 0 := by simp [partialSum]

example : partialSum 2 = (1, 1 / 4) := by
  rw [partialSum, show Finset.Icc 1 2 = {1, 2} from rfl]
  norm_num [direction, Prod.smul_mk, Prod.mk_add_mk]

end MathlibExt.Analysis.SpecificLimits.AlternatingPairWeightedSeriesConvergesWanted
