/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.CompetingRisks
import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

open Finset
open MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.CompetingRisks

namespace MathlibExtTest.Probability.Statistics.CompetingRisks

/-- With no observation times, every cumulative incidence vanishes. -/
example {r : ℕ} (D : CompetingRiskData 0 r) (c : Fin r) (t : ℝ) :
    D.cumulativeIncidence c t = 0 := by
  simp [CompetingRiskData.cumulativeIncidence]

/-- Non-vacuity witness: three subjects observed at times `1, 2, 3`, two causes: a cause-`1`
failure at `1`, a cause-`0` failure at `2`, a censoring at `3`. -/
noncomputable def D₀ : CompetingRiskData 3 2 where
  time := ![1, 2, 3]
  strictMono_time := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  events := ![![0, 1], ![1, 0], ![0, 0]]
  censored := ![0, 0, 1]

theorem D₀_totalEvents : D₀.totalEvents 0 = 1 ∧ D₀.totalEvents 1 = 1 ∧ D₀.totalEvents 2 = 0 := by
  decide

theorem D₀_atRisk : D₀.atRisk 0 = 3 ∧ D₀.atRisk 1 = 2 ∧ D₀.atRisk 2 = 1 := by decide

/-- The overall survival before `t = 2` is `1 - 1/3 = 2/3`. -/
theorem D₀_survivalBefore_one : D₀.survivalBefore 1 = 2 / 3 := by
  have hset : univ.filter (fun l : Fin 3 => l < 1) = {0} := by decide
  obtain ⟨h0, -, -⟩ := D₀_totalEvents
  obtain ⟨a0, -, -⟩ := D₀_atRisk
  rw [D₀.survivalBefore_eq, hset, prod_singleton, h0, a0]
  norm_num

/-- `F̂₀(2) = (2/3) · (1/2) = 1/3`. -/
theorem D₀_cumulativeIncidence_zero_two : D₀.cumulativeIncidence 0 2 = 1 / 3 := by
  have hset : univ.filter (fun j : Fin 3 => D₀.time j ≤ 2) = {0, 1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    fin_cases j <;> norm_num [D₀]
  obtain ⟨-, a1, -⟩ := D₀_atRisk
  rw [CompetingRiskData.cumulativeIncidence, hset, sum_pair (by decide),
    CompetingRiskData.cifIncrement, CompetingRiskData.cifIncrement, D₀_survivalBefore_one, a1]
  norm_num [D₀]

/-- The leftover overall survival is `(2/3) · (1/2) · 1 = 1/3`. -/
theorem D₀_kmTail : D₀.toCensoredData.kmTail = 1 / 3 := by
  obtain ⟨h0, h1, h2⟩ := D₀_totalEvents
  obtain ⟨a0, a1, a2⟩ := D₀_atRisk
  simp only [CensoredData.kmTail, CensoredData.kmFactor, Fin.prod_univ_three,
    CompetingRiskData.toCensoredData_deaths, CompetingRiskData.atRisk_toCensoredData,
    h0, h1, h2, a0, a1, a2]
  norm_num

/-- Treating the competing cause `1` as censoring gives the cause-`0` data
`deaths = (0, 1, 0)`, `censored = (1, 0, 1)`. -/
noncomputable def naive₀ : CensoredData 3 where
  time := D₀.time
  strictMono_time := D₀.strictMono_time
  deaths := ![0, 1, 0]
  censored := ![1, 0, 1]

/-- The naive estimate `1 - KM` of the cause-`0` incidence at `t = 2` is `1/2`. -/
theorem naive₀_one_sub_kmSurvival_two : 1 - naive₀.kmSurvival 2 = 1 / 2 := by
  have hset : univ.filter (fun j : Fin 3 => naive₀.time j ≤ 2) = {0, 1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    fin_cases j <;> norm_num [naive₀, D₀]
  have a0 : naive₀.atRisk 0 = 3 := by decide
  have a1 : naive₀.atRisk 1 = 2 := by decide
  rw [CensoredData.kmSurvival, hset, prod_pair (by decide), CensoredData.kmFactor,
    CensoredData.kmFactor, a0, a1]
  norm_num [naive₀]

/-- Censoring the competing cause overstates the cumulative incidence: `1/3 < 1/2`. -/
example : D₀.cumulativeIncidence 0 2 < 1 - naive₀.kmSurvival 2 := by
  rw [D₀_cumulativeIncidence_zero_two, naive₀_one_sub_kmSurvival_two]
  norm_num

/-- The general bounds and monotonicity, instantiated. -/
example : 0 ≤ D₀.cumulativeIncidence 1 2 ∧ D₀.cumulativeIncidence 1 2 ≤ 1 ∧
    D₀.cumulativeIncidence 1 1 ≤ D₀.cumulativeIncidence 1 3 :=
  ⟨D₀.cumulativeIncidence_nonneg 1 2, D₀.cumulativeIncidence_le_one 1 2,
    D₀.cumulativeIncidence_mono 1 (by norm_num)⟩

/-- Mass conservation on the fixture. -/
example : (∑ c, ∑ j, D₀.cifIncrement j c) + D₀.toCensoredData.kmTail = 1 :=
  D₀.sum_cumulativeIncidence_add_kmTail

/-- A single observation time with two causes: the increments split the Kaplan–Meier jump. -/
noncomputable def D₁ : CompetingRiskData 1 2 where
  time := ![0]
  strictMono_time := Subsingleton.strictMono _
  events := ![![1, 2]]
  censored := ![1]

example : D₁.cifIncrement 0 0 = 1 / 4 ∧ D₁.cifIncrement 0 1 = 1 / 2 := by
  have hset : univ.filter (fun l : Fin 1 => l < 0) = ∅ := by decide
  have a0 : D₁.atRisk 0 = 4 := by decide
  simp only [CompetingRiskData.cifIncrement, CompetingRiskData.survivalBefore, hset,
    prod_empty, a0]
  norm_num [D₁]

example : ∑ c, D₁.cifIncrement 0 c = D₁.toCensoredData.kmMass 0 := D₁.sum_cifIncrement 0

/-- With a single cause, the increment is the Kaplan–Meier jump. -/
example (D : CompetingRiskData 3 1) (j : Fin 3) :
    D.cifIncrement j 0 = D.toCensoredData.kmMass j :=
  D.cifIncrement_of_single_cause j

end MathlibExtTest.Probability.Statistics.CompetingRisks
