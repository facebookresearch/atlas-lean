/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.AalenJohansenProductIntegral
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open Finset Matrix
open MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.CompetingRisks
open MathlibExt.Probability.Statistics.AalenJohansenProductIntegral

namespace MathlibExtTest.Probability.Statistics.AalenJohansenProductIntegral

/-! ### The two-interval partition `{0, 1, 2}` of `[0, 2]` -/

/-- The partition `0 < 1 < 2` of `[0, 2]`. -/
noncomputable def P₀ : Partition 0 2 :=
  ⟨{0, 1, 2}, by simp, by simp, fun x hx => by
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> norm_num⟩

theorem sort_P₀ : P₀.1.sort (· ≤ ·) = [0, 1, 2] := by
  change ({0, 1, 2} : Finset ℝ).sort (· ≤ ·) = [0, 1, 2]
  rw [sort_insert _ (by norm_num) (by norm_num), sort_insert _ (by norm_num) (by norm_num),
    sort_singleton]

/-- From the definition, the product over `{0, 1, 2}` is
`(I + Λ(1) - Λ(0)) (I + Λ(2) - Λ(1))`. -/
theorem partitionProd_P₀ {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : ℝ → Matrix ι ι ℝ) :
    partitionProd Λ P₀.1 = (1 + (Λ 1 - Λ 0)) * (1 + (Λ 2 - Λ 1)) := by
  rw [partitionProd, sort_P₀, chainProd_cons_cons, chainProd_cons_cons, chainProd_singleton,
    mul_one]

/-! ### A three-state competing-risks model (two causes) -/

/-- Five subjects observed at times `1, 2`: at `1`, one failure from each cause and one
censoring; at `2`, one cause-`0` failure and one censoring. -/
noncomputable def D₀ : CompetingRiskData 2 2 where
  time := ![1, 2]
  strictMono_time := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i; norm_num
  events := ![![1, 1], ![1, 0]]
  censored := ![1, 1]

theorem D₀_atRisk : D₀.atRisk 0 = 5 ∧ D₀.atRisk 1 = 2 := by decide

theorem D₀_totalEvents : D₀.totalEvents 0 = 2 ∧ D₀.totalEvents 1 = 1 := by decide

/-- The partition product over `{0, 1, 2}` of the Nelson–Aalen intensity, computed by hand: with
`ΔΛ(1) = [[-2/5, 1/5, 1/5], 0, 0]` and `ΔΛ(2) = [[-1/2, 1/2, 0], 0, 0]`, the first row of
`(I + ΔΛ(1)) (I + ΔΛ(2))` is `(3/10, 1/2, 1/5)`. -/
theorem D₀_partitionProd :
    partitionProd D₀.toMultiState.naCumHazard P₀.1 none none = 3 / 10 ∧
      partitionProd D₀.toMultiState.naCumHazard P₀.1 none (some 0) = 1 / 2 ∧
      partitionProd D₀.toMultiState.naCumHazard P₀.1 none (some 1) = 1 / 5 := by
  obtain ⟨a0, a1⟩ := D₀_atRisk
  rw [partitionProd_P₀]
  unfold MultiStateData.naCumHazard stepCumHazard MultiStateData.naIncrement
  simp only [CompetingRiskData.toMultiState, Option.elim_none, Option.elim_some, a0, a1,
    sum_erase_eq_sub (mem_univ _), Fintype.sum_option, Fin.sum_univ_two, mul_apply,
    Matrix.add_apply, Matrix.sub_apply, one_apply]
  simp [D₀]
  norm_num

/-- `F̂₀(2) = 1/5 + (3/5)(1/2) = 1/2`, from the increment form of `CompetingRisks.lean`. -/
theorem D₀_cumulativeIncidence_zero : D₀.cumulativeIncidence 0 2 = 1 / 2 := by
  have hset : univ.filter (fun j : Fin 2 => D₀.time j ≤ 2) = {0, 1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    fin_cases j <;> norm_num [D₀]
  have hlt0 : univ.filter (fun l : Fin 2 => l < 0) = ∅ := by decide
  have hlt1 : univ.filter (fun l : Fin 2 => l < 1) = {0} := by decide
  obtain ⟨a0, a1⟩ := D₀_atRisk
  obtain ⟨d0, -⟩ := D₀_totalEvents
  rw [CompetingRiskData.cumulativeIncidence, hset, sum_pair (by decide),
    CompetingRiskData.cifIncrement, CompetingRiskData.cifIncrement,
    D₀.survivalBefore_eq, D₀.survivalBefore_eq, hlt0, hlt1, prod_empty, prod_singleton, d0, a0, a1]
  norm_num [D₀]

/-- `F̂₁(2) = 1/5 + (3/5) · 0 = 1/5`. -/
theorem D₀_cumulativeIncidence_one : D₀.cumulativeIncidence 1 2 = 1 / 5 := by
  have hset : univ.filter (fun j : Fin 2 => D₀.time j ≤ 2) = {0, 1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    fin_cases j <;> norm_num [D₀]
  have hlt0 : univ.filter (fun l : Fin 2 => l < 0) = ∅ := by decide
  have hlt1 : univ.filter (fun l : Fin 2 => l < 1) = {0} := by decide
  obtain ⟨a0, a1⟩ := D₀_atRisk
  obtain ⟨d0, -⟩ := D₀_totalEvents
  rw [CompetingRiskData.cumulativeIncidence, hset, sum_pair (by decide),
    CompetingRiskData.cifIncrement, CompetingRiskData.cifIncrement,
    D₀.survivalBefore_eq, D₀.survivalBefore_eq, hlt0, hlt1, prod_empty, prod_singleton, d0, a0, a1]
  norm_num [D₀]

/-- `Ŝ(2) = (3/5)(1/2) = 3/10`, the Kaplan–Meier survival of the cause-blind data. -/
theorem D₀_kmSurvival : D₀.toCensoredData.kmSurvival 2 = 3 / 10 := by
  have hset : univ.filter (fun j : Fin 2 => D₀.toCensoredData.time j ≤ 2) = univ := by
    ext j
    simp only [mem_filter, mem_univ, true_and, iff_true]
    fin_cases j <;> norm_num [D₀]
  obtain ⟨a0, a1⟩ := D₀_atRisk
  obtain ⟨d0, d1⟩ := D₀_totalEvents
  rw [CensoredData.kmSurvival, hset, Fin.prod_univ_two, CensoredData.kmFactor,
    CensoredData.kmFactor, CompetingRiskData.toCensoredData_deaths,
    CompetingRiskData.atRisk_toCensoredData, CompetingRiskData.atRisk_toCensoredData, d0, d1, a0,
    a1]
  norm_num

/-- **The hand-computed product over the two-interval partition equals the increment form**:
`P_{0,c}` is the cumulative incidence `F̂_c(2)` and `P_{00}` is `Ŝ(2)`, each side computed from its
own definition. -/
example : partitionProd D₀.toMultiState.naCumHazard P₀.1 none (some 0) =
      D₀.cumulativeIncidence 0 2 ∧
    partitionProd D₀.toMultiState.naCumHazard P₀.1 none (some 1) = D₀.cumulativeIncidence 1 2 ∧
    partitionProd D₀.toMultiState.naCumHazard P₀.1 none none = D₀.toCensoredData.kmSurvival 2 := by
  obtain ⟨h00, h01, h02⟩ := D₀_partitionProd
  rw [h00, h01, h02, D₀_cumulativeIncidence_zero, D₀_cumulativeIncidence_one, D₀_kmSurvival]
  exact ⟨rfl, rfl, rfl⟩

/-- The general theorems agree with the hand computation: `{0, 1, 2}` contains both jump times, so
its product already is the Aalen–Johansen matrix, whose first row is the increment form. -/
example : partitionProd D₀.toMultiState.naCumHazard P₀.1 =
    D₀.toMultiState.transitionMatrix 0 2 := by
  refine partitionProd_stepCumHazard _ D₀.strictMono_time _ P₀ fun j _ _ => ?_
  fin_cases j <;> simp [P₀, D₀]

example : D₀.toMultiState.transitionMatrix 0 2 none (some 0) = 1 / 2 := by
  rw [D₀.transitionMatrix_none_some (fun j => by fin_cases j <;> norm_num [D₀]),
    D₀_cumulativeIncidence_zero]

example {M : Matrix (Option (Fin 2)) (Option (Fin 2)) ℝ}
    (hM : HasProdIntegral D₀.toMultiState.naCumHazard 0 2 M) :
    M none (some 0) = 1 / 2 ∧ M none none = 3 / 10 := by
  obtain ⟨h1, h2⟩ := D₀.eq_of_hasProdIntegral (by norm_num)
    (fun j => by fin_cases j <;> norm_num [D₀]) hM
  rw [h1, h2, D₀_cumulativeIncidence_zero, D₀_kmSurvival]
  exact ⟨rfl, rfl⟩

/-- The Aalen–Johansen matrix of the fixture is stochastic. -/
example : ∑ l, D₀.toMultiState.transitionMatrix 0 2 none l = 1 :=
  D₀.toMultiState.transitionMatrix_sum_row 0 2 none

/-! ### A zero increment -/

/-- Four subjects observed at times `1, 2`: at `1`, one cause-`0` failure and one censoring; at
`2`, two censorings and no failure, so the Nelson–Aalen jump at `2` is the zero matrix. -/
noncomputable def D₁ : CompetingRiskData 2 2 where
  time := ![1, 2]
  strictMono_time := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i; norm_num
  events := ![![1, 0], ![0, 0]]
  censored := ![1, 2]

theorem D₁_atRisk : D₁.atRisk 0 = 4 ∧ D₁.atRisk 1 = 2 := by decide

/-- The Nelson–Aalen jump at the failure-free time is zero. -/
theorem D₁_naIncrement_one : D₁.toMultiState.naIncrement 1 = 0 := by
  ext h l
  cases h <;> cases l
  all_goals (try rename_i c; fin_cases c)
  all_goals simp [MultiStateData.naIncrement, CompetingRiskData.toMultiState, D₁]

/-- With a zero increment the second factor is `I`, and the partition product over `{0, 1, 2}`
has first row `(3/4, 1/4, 0)`. -/
theorem D₁_partitionProd :
    partitionProd D₁.toMultiState.naCumHazard P₀.1 none none = 3 / 4 ∧
      partitionProd D₁.toMultiState.naCumHazard P₀.1 none (some 0) = 1 / 4 ∧
      partitionProd D₁.toMultiState.naCumHazard P₀.1 none (some 1) = 0 := by
  obtain ⟨a0, a1⟩ := D₁_atRisk
  rw [partitionProd_P₀]
  unfold MultiStateData.naCumHazard stepCumHazard MultiStateData.naIncrement
  simp only [CompetingRiskData.toMultiState, Option.elim_none, Option.elim_some, a0, a1,
    sum_erase_eq_sub (mem_univ _), Fintype.sum_option, Fin.sum_univ_two, mul_apply,
    Matrix.add_apply, Matrix.sub_apply, one_apply]
  simp [D₁]
  norm_num

/-- `F̂₀(2) = 1/4 + (3/4) · 0 = 1/4` from the increment form. -/
theorem D₁_cumulativeIncidence_zero : D₁.cumulativeIncidence 0 2 = 1 / 4 := by
  have hset : univ.filter (fun j : Fin 2 => D₁.time j ≤ 2) = {0, 1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    fin_cases j <;> norm_num [D₁]
  have hlt0 : univ.filter (fun l : Fin 2 => l < 0) = ∅ := by decide
  have hlt1 : univ.filter (fun l : Fin 2 => l < 1) = {0} := by decide
  have d0 : D₁.totalEvents 0 = 1 := by decide
  obtain ⟨a0, a1⟩ := D₁_atRisk
  rw [CompetingRiskData.cumulativeIncidence, hset, sum_pair (by decide),
    CompetingRiskData.cifIncrement, CompetingRiskData.cifIncrement,
    D₁.survivalBefore_eq, D₁.survivalBefore_eq, hlt0, hlt1, prod_empty, prod_singleton, d0, a0, a1]
  norm_num [D₁]

/-- On the zero-increment fixture the hand-computed product equals the increment form. -/
example : partitionProd D₁.toMultiState.naCumHazard P₀.1 none (some 0) =
    D₁.cumulativeIncidence 0 2 := by
  rw [D₁_partitionProd.2.1, D₁_cumulativeIncidence_zero]

/-- The zero increment contributes the identity: the Aalen–Johansen matrix over `(1, 2]` is `I`,
so by Chapman–Kolmogorov the matrix over `(0, 2]` equals the one over `(0, 1]`. -/
theorem D₁_transitionMatrix_one_two : D₁.toMultiState.transitionMatrix 1 2 = 1 := by
  rw [MultiStateData.transitionMatrix, jumpProd,
    orderedProd_congr _ (act' := fun j => j = 1) fun j => by
      fin_cases j <;> simp [CompetingRiskData.toMultiState, D₁],
    orderedProd_of_unique (act := fun j : Fin 2 => j = 1) _ 1 rfl fun _ h => h,
    D₁_naIncrement_one, add_zero]

example : D₁.toMultiState.transitionMatrix 0 2 = D₁.toMultiState.transitionMatrix 0 1 := by
  rw [← D₁.toMultiState.transitionMatrix_mul (by norm_num : (0 : ℝ) ≤ 1) (by norm_num),
    D₁_transitionMatrix_one_two, mul_one]

/-! ### Degenerate cases -/

/-- With no observation times the product-integral is the identity. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (time : Fin 0 → ℝ) (A : Fin 0 → Matrix ι ι ℝ)
    {s t : ℝ} (hst : s ≤ t) : HasProdIntegral (stepCumHazard time A) s t 1 :=
  hasProdIntegral_stepCumHazard time (fun i => i.elim0) A hst

/-- Over a single point the product-integral of any `Λ` is the identity. -/
example {ι : Type*} [Fintype ι] [DecidableEq ι] (Λ : ℝ → Matrix ι ι ℝ) (s : ℝ) :
    HasProdIntegral Λ s s 1 := by
  refine tendsto_const_nhds.congr fun P => ?_
  have : P.1 = {s} := eq_singleton_iff_unique_mem.2
    ⟨P.2.1, fun x hx => le_antisymm (P.2.2.2 x hx).2 (P.2.2.2 x hx).1⟩
  rw [this, partitionProd, sort_singleton, chainProd_singleton]

end MathlibExtTest.Probability.Statistics.AalenJohansenProductIntegral
