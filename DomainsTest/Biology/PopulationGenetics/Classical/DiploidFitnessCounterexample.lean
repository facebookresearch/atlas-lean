/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Classical.DiploidFitnessCounterexample

open MathlibExt.Biology.PopulationGenetics.Selection
open MathlibExt.Biology.StatisticalGenetics.FisherDecomposition
open MathlibExt.Biology.PopulationGenetics.Classical.DiploidFitnessCounterexample

private noncomputable def p : Bool → ℝ := fun _ => 1 / 2
private def w : Bool → Bool → ℝ := fun i j => if i || j then 1 else 0

example : diploidMeanFitness p w = 3 / 4 ∧
    diploidSelect p w true = 2 / 3 ∧ diploidSelect p w false = 1 / 3 ∧
    diploidMeanFitness (diploidSelect p w) w = 8 / 9 ∧
    diploidMeanFitness (diploidSelect p w) w - diploidMeanFitness p w = 5 / 36 := by
  obtain ⟨hmean, hA, ha, hnext, hdelta, -⟩ := diploid_mean_fitness_change_ne_add_var_div_mean
  exact ⟨hmean, hA, ha, hnext, hdelta⟩

example : avgEffect p w true = 1 / 4 ∧ avgEffect p w false = -(1 / 4) ∧
    addVar p w = 1 / 8 ∧ addVar p w / diploidMeanFitness p w = 1 / 6 := by
  obtain ⟨-, -, -, -, -, hA, ha, hvar, hratio, -⟩ :=
    diploid_mean_fitness_change_ne_add_var_div_mean
  exact ⟨hA, ha, hvar, hratio⟩

example :
    let delta := diploidMeanFitness (diploidSelect p w) w - diploidMeanFitness p w
    let ratio := addVar p w / diploidMeanFitness p w
    delta ≠ ratio ∧ delta - ratio = -(1 / 36) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, hgap⟩ := diploid_mean_fitness_change_ne_add_var_div_mean
  exact hgap
