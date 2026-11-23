/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.FStatisticsExamples

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Biology.PopulationGenetics.FStatistics
  MathlibExt.Biology.PopulationGenetics.FStatisticsExamples

namespace MathlibExtTest.Biology.PopulationGenetics.FStatisticsExamples

example : gaussianDriftModel.len () = 1 := rfl

example : 0 ≤ gaussianDriftModel.len () := gaussianDriftModel.len_nonneg ()

example : MemLp (gaussianDriftModel.freq ()) 2 (gaussianReal 0 1) :=
  gaussianDriftModel.memLp_freq ()

example (ω : ℝ) : gaussianDriftModel.freq () ω = 1 / 2 + ω :=
  gaussianDriftModel_freq ω

example : gaussianDriftModel.freq () 1 = 3 / 2 := by
  rw [gaussianDriftModel_freq]
  norm_num

example : gaussianDriftModel.freq () (-1) = -1 / 2 := by
  rw [gaussianDriftModel_freq]
  norm_num

example :
    0 < gaussianReal 0 1 {ω | gaussianDriftModel.freq () ω ∉ Set.Icc (0 : ℝ) 1} :=
  gaussianDriftModel_freq_not_mem_Icc_pos

#print axioms gaussianDriftModel_freq
#print axioms gaussianDriftModel_freq_not_mem_Icc_pos

end MathlibExtTest.Biology.PopulationGenetics.FStatisticsExamples
