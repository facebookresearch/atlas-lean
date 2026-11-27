/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Bioinformatics.ZIPFA

/-! # Regressions for the zero-inflated Poisson factor law -/

set_option autoImplicit false

namespace Cslib.Bioinformatics.ZIPFA.Tests

open MeasureTheory Real
open MathlibExt.Probability.Statistics.PoissonLikelihood (poissonLik)

private noncomputable def rankZero : Parameters 2 1 0 where
  scores := fun _ k => Fin.elim0 k
  loadings := fun _ k => Fin.elim0 k
  offset := fun i => if i = 0 then 2 else 3
  offset_pos := by intro i; split <;> norm_num
  shape := 1
  shape_pos := by norm_num
  dimension_lt := by decide

private theorem rankZero_mean_first : (rankZero.mean 0 0 : ℝ) = 2 := by
  change (2 : ℝ) * exp (rankZero.logRate 0 0) = 2
  norm_num [Parameters.logRate]

private theorem rankZero_mean_second : (rankZero.mean 1 0 : ℝ) = 3 := by
  change (3 : ℝ) * exp (rankZero.logRate 1 0) = 3
  norm_num [Parameters.logRate]

private theorem rankZero_zeroProb (i : Fin 2) : (rankZero.zeroProb i 0 : ℝ) = 1 / 2 := by
  change sigmoid (-(rankZero.shape * rankZero.logRate i 0)) = _
  norm_num [Parameters.logRate, rankZero, sigmoid_zero]

-- The offset changes the Poisson mean, but not the structural-zero probability.
example : (rankZero.cellLaw 0 0).real {0} = 1 / 2 + 1 / 2 * exp (-2) := by
  change (zipMeasure _ _).real {0} = _
  rw [zipMeasure_real_zero, rankZero_mean_first, rankZero_zeroProb]
  ring

-- A positive count has no structural term.
example : (rankZero.cellLaw 0 0).real {1} = exp (-2) := by
  change (zipMeasure _ _).real {1} = _
  rw [zipMeasure_real_singleton, rankZero_zeroProb]
  norm_num [poissonLik, rankZero_mean_first, Nat.factorial]
  ring

-- The array mass multiplies a zero-cell mass at offset 2 by a positive-cell mass at offset 3.
example : rankZero.countLaw.real {fun ij => if ij.1 = 0 then 0 else 1} =
    (1 / 2 + 1 / 2 * exp (-2)) * (3 / 2 * exp (-3)) := by
  rw [rankZero.countLaw_real_singleton, Fintype.prod_prod_type, Fin.prod_univ_two]
  simp only [Fin.prod_univ_one, rankZero_zeroProb, rankZero_mean_first, rankZero_mean_second]
  norm_num [poissonLik, Nat.factorial]
  simp
  left
  ring

private noncomputable def twoFactors : Parameters 3 3 2 where
  scores := fun _ k => if k = 0 then 2 else -1
  loadings := fun _ k => if k = 0 then 3 else 4
  offset := fun _ => 3
  offset_pos := by intro i; norm_num
  shape := 3
  shape_pos := by norm_num
  dimension_lt := by decide

private theorem twoFactors_logRate : twoFactors.logRate 0 0 = 2 := by
  norm_num [Parameters.logRate, twoFactors, Fin.sum_univ_two]

-- The two factors contribute with their signs, and the offset is applied after exponentiation.
example : (twoFactors.mean 0 0 : ℝ) = 3 * exp 2 := by
  change (3 : ℝ) * exp (twoFactors.logRate 0 0) = _
  rw [twoFactors_logRate]

-- The shared shape multiplies the normalized log-rate rather than the log of the offset mean.
example : log ((twoFactors.zeroProb 0 0 : ℝ) / (1 - (twoFactors.zeroProb 0 0 : ℝ))) = -6 := by
  rw [twoFactors.log_odds_zeroProb, twoFactors_logRate]
  norm_num [twoFactors]

end Cslib.Bioinformatics.ZIPFA.Tests
