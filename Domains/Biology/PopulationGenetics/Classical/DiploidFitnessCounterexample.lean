/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Selection
public import Domains.Biology.StatisticalGenetics.FisherDecomposition
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-!
# A diploid mean-fitness counterexample

The change in mean fitness over one generation need not equal the additive genetic variance
in fitness divided by the initial mean fitness. This is a direct calculation, not a claim
about Fisher's theorem itself. For context, see J. Felsenstein, *Theoretical Evolutionary
Genetics* (December 2019), §II.8, p. 94.
-/

public section

namespace MathlibExt.Biology.PopulationGenetics.Classical.DiploidFitnessCounterexample

open Selection
open StatisticalGenetics.FisherDecomposition

/-- For two equally frequent alleles (`true` is `A`, `false` is `a`), all genotypes have fitness
one except `aa`, which has fitness zero. After diploid viability selection, the allele
frequencies are `2/3` and `1/3`, and mean fitness rises from `3/4` to `8/9`. The average effects
are `1/4` and `-1/4`, giving additive genetic variance `1/8`. The change `5/36` is not the ratio
`1/6` of the variance to the initial mean; the signed difference is `-1/36`. -/
theorem diploid_mean_fitness_change_ne_add_var_div_mean :
    let p : Bool → ℝ := fun _ => 1 / 2
    let w : Bool → Bool → ℝ := fun i j => if i || j then 1 else 0
    let p' := diploidSelect p w
    let mean := diploidMeanFitness p w
    let nextMean := diploidMeanFitness p' w
    let delta := nextMean - mean
    let variance := addVar p w
    let ratio := variance / mean
    mean = 3 / 4 ∧ p' true = 2 / 3 ∧ p' false = 1 / 3 ∧ nextMean = 8 / 9 ∧
      delta = 5 / 36 ∧ avgEffect p w true = 1 / 4 ∧ avgEffect p w false = -(1 / 4) ∧
      variance = 1 / 8 ∧ ratio = 1 / 6 ∧ delta ≠ ratio ∧ delta - ratio = -(1 / 36) := by
  intro p w p' mean nextMean delta variance ratio
  have hmean : diploidMeanFitness p w = 3 / 4 := by
    norm_num [diploidMeanFitness, Fintype.sum_bool, p, w]
  have hA : p' true = 2 / 3 := by
    simp only [p', diploidSelect, hmean]
    norm_num [marginalFitness, Fintype.sum_bool, p, w]
  have ha : p' false = 1 / 3 := by
    simp only [p', diploidSelect, hmean]
    norm_num [marginalFitness, Fintype.sum_bool, p, w]
  have hnext : nextMean = 8 / 9 := by
    norm_num [nextMean, diploidMeanFitness, Fintype.sum_bool, hA, ha, w]
  have hdelta : delta = 5 / 36 := by
    norm_num [delta, mean, hnext, hmean]
  have hvalue : meanValue p w = 3 / 4 := hmean
  have hEffectA : avgEffect p w true = 1 / 4 := by
    rw [avgEffect, hvalue]
    norm_num [Fintype.sum_bool, p, w]
  have hEffecta : avgEffect p w false = -(1 / 4) := by
    rw [avgEffect, hvalue]
    norm_num [Fintype.sum_bool, p, w]
  have hvar : addVar p w = 1 / 8 := by
    norm_num [addVar, Fintype.sum_bool, hEffectA, hEffecta, p]
  have hratio : ratio = 1 / 6 := by
    norm_num [ratio, variance, mean, hvar, hmean]
  refine ⟨hmean, hA, ha, hnext, hdelta, hEffectA, hEffecta, hvar, hratio, ?_, ?_⟩ <;>
    norm_num [hdelta, hratio]

end MathlibExt.Biology.PopulationGenetics.Classical.DiploidFitnessCounterexample
