/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.DerSimonianLaird

namespace MathlibExtTest.Probability.Statistics.DerSimonianLaird

open WantedExt.Probability.Statistics.DerSimonianLairdWanted

/-- With unit sampling and between-study variances, estimates `0` and `2` give estimator,
pooled mean, and pooled variance all equal to `1`. -/
example : dlEstimator (fun _ : Fin 2 => 1) ![0, 2] = 1 ∧
    pooledEstimate (fun _ : Fin 2 => 1) 1 ![0, 2] = 1 ∧
    (∑ _i : Fin 2, ((1 : ℝ) + 1)⁻¹)⁻¹ = 1 := by
  have h := equal_variances le_rfl 1 one_pos ![0, 2] 1 zero_le_one
  rw [h.1, h.2.1, h.2.2]
  norm_num [Fin.sum_univ_two, max_def]

/-- With identical observations, the negative untruncated estimate is cut off at zero. -/
example : dlEstimator (fun _ : Fin 2 => 1) (fun _ => 3) = 0 := by
  have h := (equal_variances le_rfl 1 one_pos (fun _ : Fin 2 => 3) 0 le_rfl).1
  norm_num [Fin.sum_univ_two, max_def] at h
  exact h

end MathlibExtTest.Probability.Statistics.DerSimonianLaird
