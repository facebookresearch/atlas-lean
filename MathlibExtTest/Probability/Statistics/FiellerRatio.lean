/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Statistics.FiellerRatio

open WantedExt.Probability.Statistics.FiellerRatioWanted

-- A zero variance can collapse the closed interval to a singleton.
example : fiellerSet 0 1 0 0 0 1 = Set.Icc 0 0 := by
  ext θ
  simp [fiellerSet, Set.Icc_self, sq_nonpos_iff]

-- The strict gap excludes neither endpoint from the confidence set.
example : fiellerSet 1 0 0 0 1 1 = (Set.Ioo (-1) 1)ᶜ := by
  ext θ
  simp only [fiellerSet, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_Ioo, mul_zero, sub_zero,
    zero_add, mul_one]
  rw [show (1 : ℝ) ^ 2 * θ ^ 2 = θ ^ 2 by rw [one_pow, one_mul], ← not_lt, sq_lt_sq,
    abs_of_nonneg (zero_le_one : (0 : ℝ) ≤ 1), abs_lt]

-- For a negative quadratic coefficient the zero threshold gives the whole line.
example : fiellerSet 0 0 0 0 1 1 = Set.univ := by
  ext θ
  simp [fiellerSet, sq_nonneg]

open MeasureTheory ProbabilityTheory in
-- The two coordinates can be perfectly correlated while the contrast still has unit variance.
example (z : ℝ) (hz : 0 < z) :
    (gaussianReal 0 1).real {x : ℝ | 2 ∈ fiellerSet x x 1 1 1 z} =
      (gaussianReal 0 1).real (Set.Icc (-z) z) := by
  let μ := gaussianReal 0 1
  let L := ContinuousLinearMap.id ℝ ℝ
  have hG : HasGaussianLaw (fun x : ℝ ↦ (x, x)) μ :=
    (IsGaussian.hasGaussianLaw_id (μ := μ)).map_fun (L.prod L)
  have hvar : Var[id; μ] = 1 := by
    simp [μ, variance_id_gaussianReal]
  have hcov : cov[id, id; μ] = 1 := by
    rw [covariance_self measurable_id.aemeasurable, hvar]
  have hmean : ∫ x : ℝ, id x ∂μ = 2 * ∫ x : ℝ, id x ∂μ := by
    change (∫ x : ℝ, x ∂gaussianReal 0 1) = 2 * ∫ x : ℝ, x ∂gaussianReal 0 1
    rw [integral_id_gaussianReal, mul_zero]
  exact measureReal_mem_fiellerSet μ id id hG 1 1 1 2 z hvar hvar hcov hmean (by norm_num) hz
