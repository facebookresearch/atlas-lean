/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Classical.PloidyBridge
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.Selection

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.PloidyBridge

/-- Frequencies of the three-type example. -/
noncomputable def p₃ : Fin 3 → ℝ := ![1 / 2, 1 / 3, 1 / 6]

/-- Haploid fitnesses of the three-type example. -/
noncomputable def v₃ : Fin 3 → ℝ := ![2, 1, 3 / 2]

theorem meanFitness_p₃ : meanFitness p₃ v₃ = 19 / 12 := by
  norm_num [meanFitness, p₃, v₃, Fin.sum_univ_three]

/-- Haploid selection moves type `0` to `(1/2 * 2) / (19/12) = 12/19`. -/
example : select p₃ v₃ 0 = 12 / 19 := by
  simp only [select, meanFitness_p₃]
  norm_num [p₃, v₃]

/-- Diploid selection with multiplicative fitnesses `v i * v j` agrees. -/
example : diploidSelect p₃ (fun i j => v₃ i * v₃ j) 0 = 12 / 19 := by
  rw [diploidSelect_eq_select_of_mul p₃ v₃ (by rw [meanFitness_p₃]; norm_num)]
  simp only [select, meanFitness_p₃]
  norm_num [p₃, v₃]

/-- The diploid mean fitness in the same example is `(19/12)^2`. -/
example : diploidMeanFitness p₃ (fun i j => v₃ i * v₃ j) = (19 / 12) ^ 2 := by
  rw [diploidMeanFitness_eq_sq_of_mul, meanFitness_p₃]

end MathlibExtTest.Biology.PopulationGenetics.Classical.PloidyBridge
