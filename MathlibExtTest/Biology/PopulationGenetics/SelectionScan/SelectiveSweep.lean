/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.SelectionScan.SelectiveSweep
public import Mathlib.Tactic.NormNum

@[expose] public section

open Real Filter Topology MeasureTheory ProbabilityTheory

open scoped NNReal
open MathlibExt.Biology.PopulationGenetics.SelectionScan

namespace MathlibExtTest.Biology.PopulationGenetics.SelectionScan.SelectiveSweep

/-! ### The logistic trajectory -/

example (s x₀ : ℝ) : sweepTraj s x₀ 0 = x₀ := sweepTraj_zero s x₀

example (t : ℝ) : sweepTraj 1 (1 / 2) t ∈ Set.Ioo (0 : ℝ) 1 :=
  sweepTraj_mem_Ioo (by norm_num) (by norm_num) 1 t

/-- The logistic equation at a concrete starting frequency. -/
example (t : ℝ) : HasDerivAt (sweepTraj 1 (1 / 2))
    (1 * sweepTraj 1 (1 / 2) t * (1 - sweepTraj 1 (1 / 2) t)) t :=
  hasDerivAt_sweepTraj (by norm_num) (by norm_num) 1 t

example : StrictMono (sweepTraj 1 (1 / 2)) :=
  sweepTraj_strictMono (by norm_num) (by norm_num) (by norm_num)

/-- The trajectory started at `1/4` reaches `3/4` exactly at `sweepDuration`. -/
example : sweepTraj 1 (1 / 4) (sweepDuration 1 (1 / 4) (3 / 4)) = 3 / 4 :=
  sweepTraj_sweepDuration (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

example : 0 < sweepDuration 1 (1 / 4) (3 / 4) :=
  sweepDuration_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- A complete sweep with `s = 1` in a population of `N = 2` diploids takes `2 log 3`. -/
example : sweepDuration 1 (1 / (2 * 2)) (1 - 1 / (2 * 2)) = 2 * log 3 := by
  rw [sweepDuration_full (by norm_num) (by norm_num : (1 : ℝ) < 2)]
  norm_num

/-! ### Star-genealogy EHH, its integral and the iHS -/

example (r T : ℝ) : sweepEhh r T 0 = 1 := sweepEhh_zero r T

/-- The pair identity probability is the square of a Poisson zero probability. -/
example (r T d : ℝ≥0) : sweepEhh r T d = ((poissonMeasure (r * d * T)).real {0}) ^ 2 :=
  sweepEhh_eq_poisson_sq r T d

example : sweepEhh 1 1 1 = exp (-2) := by
  rw [sweepEhh]
  norm_num

example : sweepEhh 1 1 2 ≤ sweepEhh 1 1 1 :=
  sweepEhh_antitone (by norm_num) (by norm_num) (by norm_num)

example : Tendsto (sweepEhh 1 1) atTop (𝓝 0) := tendsto_sweepEhh_atTop one_pos one_pos

/-- The integrated haplotype homozygosity of a star of age `1` with `r = 1` is `1/2`. -/
example : ihh 1 1 = 1 / 2 := by
  rw [ihh_eq one_pos one_pos]
  norm_num

/-- A younger derived star (age `1`) against an older ancestral star (age `2`) gives a
negative integrated haplotype score. -/
example : ihs 1 2 1 = log (1 / 2) :=
  ihs_eq_log_div one_pos (by norm_num) one_pos

example : ihs 1 2 1 < 0 := (ihs_neg_iff one_pos (by norm_num) one_pos).mpr (by norm_num)

/-- A longer-lived ancestral allele would give a positive score. -/
example : ¬ ihs 1 1 2 < 0 := by
  rw [ihs_neg_iff one_pos one_pos (by norm_num)]
  norm_num

/-- The power law after a complete sweep: with `r = 1`, `s = 1`, `N = 2` and `d = 1` the
extended haplotype homozygosity is `3 ^ (-4)`. -/
example : sweepEhh 1 (sweepDuration 1 (1 / (2 * 2)) (1 - 1 / (2 * 2))) 1
    = (2 * 2 - 1 : ℝ) ^ (-(4 * 1 * 1 / 1) : ℝ) :=
  sweepEhh_sweepDuration_full one_pos (by norm_num)

#print axioms sweepDuration_full
#print axioms ihh_eq
#print axioms sweepEhh_sweepDuration_full

end MathlibExtTest.Biology.PopulationGenetics.SelectionScan.SelectiveSweep
