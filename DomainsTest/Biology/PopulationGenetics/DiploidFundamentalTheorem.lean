/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.DiploidFundamentalTheorem
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.NormNum

import Mathlib.Tactic.FinCases

/-!
# Tests for the diploid fundamental theorem

Concrete two-allele witnesses: under overdominance the partial change equals `V_A / w̄` while the
total change differs from it; under genic (additive) fitnesses both coincide; the symmetry
hypothesis is load-bearing for the marginal-fitness identity.
-/

@[expose] public section

open MathlibExt.Biology.PopulationGenetics.Selection
open MathlibExt.Biology.StatisticalGenetics.FisherDecomposition
open Domains.Biology.PopulationGenetics.DiploidFundamentalTheorem

namespace DomainsTest.Biology.PopulationGenetics.DiploidFundamentalTheorem

/-- Overdominant fitnesses: heterozygotes have fitness `2`, homozygotes `1`. -/
noncomputable def wOver : Fin 2 → Fin 2 → ℝ := ![![1, 2], ![2, 1]]

/-- Genic fitnesses `1 + s_i + s_j` with `s = (1, 0)`: no dominance. -/
noncomputable def wGenic : Fin 2 → Fin 2 → ℝ := ![![3, 2], ![2, 1]]

/-- Asymmetric ordered fitnesses. -/
noncomputable def wAsym : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![3, 1]]

/-- Allele frequencies `(1/4, 3/4)`. -/
noncomputable def pQ : Fin 2 → ℝ := ![1 / 4, 3 / 4]

/-- Allele frequencies `(1/2, 1/2)`. -/
noncomputable def pH : Fin 2 → ℝ := ![1 / 2, 1 / 2]

theorem wOver_symm : ∀ i j, wOver i j = wOver j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [wOver]

theorem wGenic_symm : ∀ i j, wGenic i j = wGenic j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [wGenic]

theorem sum_pQ : ∑ i, pQ i = 1 := by
  norm_num [pQ, Fin.sum_univ_two]

/-- The partial change equals `V_A / w̄ = 3/44` under overdominance. -/
example : 2 * ∑ i, avgEffect pQ wOver i * (diploidSelect pQ wOver i - pQ i) = 3 / 44 := by
  rw [two_mul_sum_avgEffect_mul_diploidSelect_sub wOver_symm
    (by norm_num [diploidMeanFitness, pQ, wOver, Fin.sum_univ_two])]
  norm_num [addVar, avgEffect, meanValue, diploidMeanFitness, pQ, wOver, Fin.sum_univ_two]

/-- The additive variance term is `3/44`. -/
example : addVar pQ wOver / diploidMeanFitness pQ wOver = 3 / 44 := by
  norm_num [addVar, avgEffect, meanValue, diploidMeanFitness, pQ, wOver, Fin.sum_univ_two]

/-- The total change is `57/968`, not `3/44`: the dominance term is `-9/968`. -/
example : diploidMeanFitness (diploidSelect pQ wOver) wOver - diploidMeanFitness pQ wOver =
    57 / 968 := by
  norm_num [avgEffect, meanValue, addVar, diploidMeanFitness, diploidSelect,
    marginalFitness, pQ, wOver, Fin.sum_univ_two]

/-- Under overdominance the total change differs from `V_A / w̄`. -/
example : diploidMeanFitness (diploidSelect pQ wOver) wOver - diploidMeanFitness pQ wOver ≠
    addVar pQ wOver / diploidMeanFitness pQ wOver := by
  norm_num [avgEffect, meanValue, addVar, diploidMeanFitness, diploidSelect,
    marginalFitness, pQ, wOver, Fin.sum_univ_two]

/-- Genic fitnesses have no dominance deviations. -/
theorem domDev_wGenic : ∀ i j, domDev pQ wGenic i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [domDev, avgEffect, meanValue, pQ, wGenic, Fin.sum_univ_two]

/-- With genic fitnesses the total change is `V_A / w̄ = 1/4`. -/
example : diploidMeanFitness (diploidSelect pQ wGenic) wGenic -
    diploidMeanFitness pQ wGenic = 1 / 4 := by
  rw [diploidMeanFitness_diploidSelect_sub_of_domDev_eq_zero sum_pQ wGenic_symm
    (by norm_num [diploidMeanFitness, pQ, wGenic, Fin.sum_univ_two]) domDev_wGenic]
  norm_num [addVar, avgEffect, meanValue, diploidMeanFitness, pQ, wGenic,
    Fin.sum_univ_two]

/-- The symmetry hypothesis of `marginalFitness_eq_add_avgEffect` is load-bearing. -/
example : marginalFitness pH wAsym 0 ≠ diploidMeanFitness pH wAsym + avgEffect pH wAsym 0 := by
  norm_num [marginalFitness, diploidMeanFitness, avgEffect, meanValue, pH, wAsym,
    Fin.sum_univ_two]

end DomainsTest.Biology.PopulationGenetics.DiploidFundamentalTheorem
