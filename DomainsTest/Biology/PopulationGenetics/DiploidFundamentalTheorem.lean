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
total change differs from it by the dominance term `-9/968` of the general total-change theorem;
under genic (additive) fitnesses both coincide; the symmetry hypothesis is needed for the
marginal-fitness identity. Both populations lie in the model domain `IsDiploidModel`. A boundary
population with "frequencies" `(2, -1)` meets every condition of the domain except `0 ≤ p`, and
there the quantity called the additive genetic variance is `-4`, while in the domain the partial
change is never negative.
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

/-- "Allele frequencies" `(2, -1)`: they sum to `1`, but the second is negative. -/
noncomputable def pOut : Fin 2 → ℝ := ![2, -1]

/-- Symmetric nonnegative fitnesses under which only the homozygote `(1, 1)` survives. -/
noncomputable def wOut : Fin 2 → Fin 2 → ℝ := ![![0, 0], ![0, 1]]

theorem wOver_symm : ∀ i j, wOver i j = wOver j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [wOver]

theorem wGenic_symm : ∀ i j, wGenic i j = wGenic j i := by
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [wGenic]

theorem sum_pQ : ∑ i, pQ i = 1 := by
  norm_num [pQ, Fin.sum_univ_two]

/-- The overdominant population at `(1/4, 3/4)` lies in the model domain. -/
theorem isDiploidModel_pQ_wOver : IsDiploidModel pQ wOver where
  freq_nonneg i := by fin_cases i <;> norm_num [pQ]
  sum_freq := sum_pQ
  fitness_nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num [wOver]
  fitness_symm := wOver_symm
  meanFitness_pos := by norm_num [diploidMeanFitness, pQ, wOver, Fin.sum_univ_two]

/-- The genic population at `(1/4, 3/4)` lies in the model domain. -/
theorem isDiploidModel_pQ_wGenic : IsDiploidModel pQ wGenic where
  freq_nonneg i := by fin_cases i <;> norm_num [pQ]
  sum_freq := sum_pQ
  fitness_nonneg i j := by fin_cases i <;> fin_cases j <;> norm_num [wGenic]
  fitness_symm := wGenic_symm
  meanFitness_pos := by norm_num [diploidMeanFitness, pQ, wGenic, Fin.sum_univ_two]

/-- Under overdominance at `(1/4, 3/4)` the first allele gains `Δp_0 = p_0 α_0 / w̄ = 3/44`. -/
example : diploidSelect pQ wOver 0 - pQ 0 = 3 / 44 := by
  rw [diploidSelect_sub_eq isDiploidModel_pQ_wOver]
  norm_num [avgEffect, meanValue, diploidMeanFitness, pQ, wOver, Fin.sum_univ_two]

/-- The partial change equals `V_A / w̄ = 3/44` under overdominance. -/
example : 2 * ∑ i, avgEffect pQ wOver i * (diploidSelect pQ wOver i - pQ i) = 3 / 44 := by
  rw [two_mul_sum_avgEffect_mul_diploidSelect_sub isDiploidModel_pQ_wOver]
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

/-- Through the general total-change theorem at the overdominant population, the additive term is
`V_A / w̄ = 3/44` and the dominance correction is `-9/968`, which does not vanish. -/
example : diploidMeanFitness (diploidSelect pQ wOver) wOver - diploidMeanFitness pQ wOver =
    3 / 44 + -9 / 968 := by
  rw [diploidMeanFitness_diploidSelect_sub_eq isDiploidModel_pQ_wOver]
  congr 1
  · norm_num [addVar, avgEffect, meanValue, diploidMeanFitness, pQ, wOver, Fin.sum_univ_two]
  · norm_num [domDev, avgEffect, meanValue, diploidMeanFitness, pQ, wOver, Fin.sum_univ_two]

/-- Through `meanValue_eq_diploidMeanFitness`, the mean genotypic value in fitness at the
overdominant population is its mean fitness `11/8`. -/
example : meanValue pQ wOver = 11 / 8 := by
  rw [meanValue_eq_diploidMeanFitness]
  norm_num [diploidMeanFitness, pQ, wOver, Fin.sum_univ_two]

/-- Through `marginalFitness_eq_add_avgEffect`, the marginal fitness of the first allele at the
overdominant population is `w̄ + α_0 = 11/8 + 3/8 = 7/4`. -/
example : marginalFitness pQ wOver 0 = 7 / 4 := by
  rw [marginalFitness_eq_add_avgEffect wOver_symm]
  norm_num [avgEffect, meanValue, diploidMeanFitness, pQ, wOver, Fin.sum_univ_two]

/-- Genic fitnesses have no dominance deviations. -/
theorem domDev_wGenic : ∀ i j, domDev pQ wGenic i j = 0 := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [domDev, avgEffect, meanValue, pQ, wGenic, Fin.sum_univ_two]

/-- With genic fitnesses the total change is `V_A / w̄ = 1/4`. -/
example : diploidMeanFitness (diploidSelect pQ wGenic) wGenic -
    diploidMeanFitness pQ wGenic = 1 / 4 := by
  rw [diploidMeanFitness_diploidSelect_sub_of_domDev_eq_zero isDiploidModel_pQ_wGenic
    domDev_wGenic]
  norm_num [addVar, avgEffect, meanValue, diploidMeanFitness, pQ, wGenic,
    Fin.sum_univ_two]

/-- The symmetry hypothesis of `marginalFitness_eq_add_avgEffect` is needed. -/
example : marginalFitness pH wAsym 0 ≠ diploidMeanFitness pH wAsym + avgEffect pH wAsym 0 := by
  norm_num [marginalFitness, diploidMeanFitness, avgEffect, meanValue, pH, wAsym,
    Fin.sum_univ_two]

/-! ### The model domain matters -/

/-- In the model domain the partial change of the fundamental theorem is never negative: it is
the additive genetic variance, a weighted sum of squares, over the positive mean fitness. -/
example {ι : Type*} [Fintype ι] {p : ι → ℝ} {w : ι → ι → ℝ} (hm : IsDiploidModel p w) :
    0 ≤ 2 * ∑ i, avgEffect p w i * (diploidSelect p w i - p i) := by
  rw [two_mul_sum_avgEffect_mul_diploidSelect_sub hm]
  exact div_nonneg (mul_nonneg zero_le_two (Finset.sum_nonneg fun i _ =>
    mul_nonneg (hm.freq_nonneg i) (sq_nonneg _))) hm.meanFitness_pos.le

/-- The boundary population `(2, -1)` lies outside the model domain. -/
theorem not_isDiploidModel_pOut_wOut : ¬ IsDiploidModel pOut wOut := by
  intro hm
  have h := hm.freq_nonneg 1
  norm_num [pOut] at h

/-- Every condition of the model domain other than `0 ≤ p` holds at the boundary population: the
"frequencies" sum to `1`, the fitnesses are nonnegative and symmetric, and the mean fitness is
`1`. -/
example : ∑ i, pOut i = 1 ∧ (∀ i j, 0 ≤ wOut i j) ∧ (∀ i j, wOut i j = wOut j i) ∧
    diploidMeanFitness pOut wOut = 1 := by
  refine ⟨by norm_num [pOut, Fin.sum_univ_two], fun i j => ?_, fun i j => ?_,
    by norm_num [diploidMeanFitness, pOut, wOut, Fin.sum_univ_two]⟩
  · fin_cases i <;> fin_cases j <;> norm_num [wOut]
  · fin_cases i <;> fin_cases j <;> norm_num [wOut]

/-- Without `0 ≤ p` the identity no longer equates the partial change with a variance: at the
boundary population the partial change is `-4`, and so is `addVar pOut wOut`, the quantity called
the additive genetic variance. -/
example : 2 * ∑ i, avgEffect pOut wOut i * (diploidSelect pOut wOut i - pOut i) = -4 ∧
    addVar pOut wOut = -4 := by
  constructor <;>
    norm_num [avgEffect, meanValue, addVar, diploidMeanFitness, diploidSelect,
      marginalFitness, pOut, wOut, Fin.sum_univ_two]

end DomainsTest.Biology.PopulationGenetics.DiploidFundamentalTheorem
