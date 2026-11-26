/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Statistics.NormalMeanMLE
import Mathlib.Tactic.NormNum

open MathlibExt.Probability.FiniteProbability ProbabilityTheory
open scoped NNReal

private def sample : Fin 3 → ℝ := ![-2, 3, 11]

private theorem sample_mean : sampleMean sample = 4 := by
  norm_num [sampleMean_eq_sum_div, sample, Fin.sum_univ_succ]

-- Use a non-unit variance and a sample whose mean is not itself an observation.
example : IsMaxOn (fun m => (gaussianMeanFamily (2 : ℝ≥0) (by norm_num)).iidLikelihood 3 m sample)
    Set.univ 4 :=
  (isMaxOn_gaussianMeanLikelihood_iff (by norm_num) (by decide) sample 4).2 sample_mean.symm

example : ¬ IsMaxOn (fun m => (gaussianMeanFamily (2 : ℝ≥0) (by norm_num)).iidLikelihood 3 m sample)
    Set.univ 3 := by
  rw [isMaxOn_gaussianMeanLikelihood_iff (hn := by decide), sample_mean]
  norm_num

-- A singleton has a unique maximizer without a positive empirical variance assumption.
example (a m : ℝ) :
    IsMaxOn (fun u => (gaussianMeanFamily (1 : ℝ≥0) one_ne_zero).iidLikelihood 1 u ![a])
      Set.univ m ↔ m = a := by
  rw [isMaxOn_gaussianMeanLikelihood_iff (hn := by decide)]
  simp [sampleMean_eq_sum_div]

-- The family used by the likelihood has the ordinary Gaussian law.
example (m : ℝ) : (gaussianMeanFamily (2 : ℝ≥0) (by norm_num)).law m = gaussianReal m 2 := by
  rw [gaussianReal_of_var_ne_zero m (by norm_num)]
  rfl

-- With no observations the likelihood is constant, so the nonempty hypothesis matters.
example (x : Fin 0 → ℝ) (m : ℝ) :
    (gaussianMeanFamily (1 : ℝ≥0) one_ne_zero).iidLikelihood 0 m x = 1 := by
  simp
