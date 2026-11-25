/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Optimization.GoemansWilliamsonConstant

@[expose] public section

open Real MathlibExt.Combinatorics.Optimization.GoemansWilliamson

namespace MathlibExtTest.Combinatorics.Optimization.GoemansWilliamsonConstant

/-- The constant lies strictly between `0.87856` and `1`. -/
example : (0.87856 : ℝ) < gwConstant ∧ gwConstant ≤ 1 := ⟨lt_gwConstant, gwConstant_le_one⟩

/-- Lemma 3.4 at `y = 0` (orthogonal vectors): `α / 2 ≤ 1 / 2`. -/
example : gwConstant * ((1 - 0) / 2) ≤ 1 / 2 := by
  have h := gwConstant_mul_le_arccos_div_pi (y := 0) (by norm_num) (by norm_num)
  rw [arccos_zero] at h
  have hpi := pi_pos
  calc gwConstant * ((1 - 0) / 2) ≤ π / 2 / π := h
    _ = 1 / 2 := by field_simp

/-- The certified inequality at `θ = π` reads `0.878565 ≤ 1`. -/
example : (0.878565 : ℝ) * ((1 - cos π) / 2) ≤ π / π :=
  certified_mul_one_sub_cos_le pi_pos.le le_rfl

/-- The certified inequality near the minimiser `θ ≈ 2.3311`, where it is tight to `10^{-5}`. -/
example : (0.878565 : ℝ) * ((1 - cos 2.3311) / 2) ≤ 2.3311 / π :=
  certified_mul_one_sub_cos_le (by norm_num) (by linarith [pi_gt_d2])

end MathlibExtTest.Combinatorics.Optimization.GoemansWilliamsonConstant
