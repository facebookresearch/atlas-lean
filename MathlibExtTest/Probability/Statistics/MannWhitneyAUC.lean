/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.MannWhitneyAUC
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tests for the empirical AUC and the Mann–Whitney statistic

A concrete two-by-two sample with one tie (`AUC = 7/8`), the all-tied boundary case
(`AUC = 1/2`), perfect separation (`AUC = 1`), and the ROC-point lemmas.
-/

@[expose] public section

open Finset ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.MannWhitneyAUC

/-- Positives `(2, 1)` and negatives `(1, 0)`: three correctly ranked pairs and one tie give
`U = 7/2` and `AUC = 7/8`. -/
example : empiricalAUC ![(2 : ℝ), 1] ![(1 : ℝ), 0] = 7 / 8 := by
  rw [empiricalAUC_eq_mannWhitneyU (by norm_num) (by norm_num)]
  simp [mannWhitneyU, Fin.sum_univ_two]
  norm_num

/-- All scores tied: the ROC curve is the diagonal and `AUC = 1/2`. -/
example : empiricalAUC ![(3 : ℝ)] ![(3 : ℝ)] = 1 / 2 := by
  rw [empiricalAUC_eq_mannWhitneyU (by norm_num) (by norm_num)]
  simp [mannWhitneyU]

/-- Perfect separation gives `AUC = 1`. -/
example : empiricalAUC ![(5 : ℝ), 4] ![(1 : ℝ)] = 1 := by
  rw [empiricalAUC_eq_mannWhitneyU (by norm_num) (by norm_num)]
  simp [mannWhitneyU, Fin.sum_univ_two]

/-- The left end of the trapezoid at score `1` is the ROC point at the next score `2`. -/
example : rocRateAbove ![(2 : ℝ), 1] 1 = rocRate ![(2 : ℝ), 1] 2 :=
  rocRateAbove_eq_rocRate_of_forall_not_mem_Ioo (by norm_num) (by
    intro i; fin_cases i <;> simp)

/-- Above the largest score the ROC curve starts at the origin. -/
example : rocRateAbove ![(2 : ℝ), 1] 2 = 0 :=
  rocRateAbove_eq_zero_of_forall_le (by intro i; fin_cases i <;> simp)

end MathlibExtTest.Probability.Statistics.MannWhitneyAUC
