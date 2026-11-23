/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecificLimits.ReciprocalSumAddInvNull

open Filter Topology

namespace MathlibExt.Analysis.SpecificLimits.ReciprocalSumAddInvNullWanted

example (a : ℕ → ℝ) : xSeq a 0 = a 0 + 1 / a 0 := by simp [xSeq]

example (n : ℕ) : xSeq (fun _ ↦ 1) n = (n + 1 : ℝ) * 2 := by
  simp [xSeq, nsmul_eq_mul, one_add_one_eq_two]

example (n : ℕ) : xSeq (fun _ ↦ 0) n = 0 := by simp [xSeq]

example : Tendsto (fun n ↦ 1 / xSeq (fun _ ↦ 1) n) atTop (𝓝 0) :=
  tendsto_one_div_sum_add_inv_zero _ (fun _ ↦ zero_lt_one)

end MathlibExt.Analysis.SpecificLimits.ReciprocalSumAddInvNullWanted
