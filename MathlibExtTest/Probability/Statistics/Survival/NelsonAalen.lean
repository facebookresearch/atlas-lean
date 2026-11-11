/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.NelsonAalen
public import MathlibExt.Probability.Statistics.Survival.LogRank
public import MathlibExt.Probability.Statistics.Survival.CoxPartialLikelihood

@[expose] public section

open Finset
open MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.LogRank
open MathlibExt.Probability.Statistics.CoxPartialLikelihood

namespace MathlibExtTest.Probability.Statistics.NelsonAalen

/-! ### No observation times -/

example (D : CensoredData 0) (t : ℝ) : D.nelsonAalen t = 0 := by
  simp [CensoredData.nelsonAalen]

example (D : CensoredData 0) (t : ℝ) : D.kmSurvival t = 1 := by
  simp [CensoredData.kmSurvival]

example (D : CensoredData 0) (t : ℝ) : D.greenwoodVariance t = 0 := by
  simp [CensoredData.greenwoodVariance]

/-! ### Three times: deaths `(1, 1, 0)`, censorings `(0, 1, 1)` -/

/-- Non-vacuity witness: four subjects; a death at `1`; a death and a censoring at `2`; a
censoring at `3`. The numbers at risk are `4, 3, 1`. -/
noncomputable def D₁ : CensoredData 3 where
  time := ![1, 2, 3]
  strictMono_time := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i <;> norm_num
  deaths := ![1, 1, 0]
  censored := ![0, 1, 1]

theorem D₁_atRisk : D₁.atRisk 0 = 4 ∧ D₁.atRisk 1 = 3 ∧ D₁.atRisk 2 = 1 := by decide

theorem D₁_filter_two : univ.filter (fun j : Fin 3 => D₁.time j ≤ 2) = {0, 1} := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
  fin_cases j <;> norm_num [D₁]

/-- `Â(2) = 1/4 + 1/3 = 7/12`. -/
theorem D₁_nelsonAalen_two : D₁.nelsonAalen 2 = 7 / 12 := by
  obtain ⟨a0, a1, -⟩ := D₁_atRisk
  rw [CensoredData.nelsonAalen, D₁_filter_two, sum_pair (by decide), a0, a1]
  norm_num [D₁]

/-- `Ŝ(2) = (3/4) (2/3) = 1/2`. -/
theorem D₁_kmSurvival_two : D₁.kmSurvival 2 = 1 / 2 := by
  obtain ⟨a0, a1, -⟩ := D₁_atRisk
  rw [CensoredData.kmSurvival, D₁_filter_two, prod_pair (by decide), CensoredData.kmFactor,
    CensoredData.kmFactor, a0, a1]
  norm_num [D₁]

/-- Greenwood: `V̂(2) = (1/2)² (1/(4·3) + 1/(3·2)) = 1/16`. -/
theorem D₁_greenwoodVariance_two : D₁.greenwoodVariance 2 = 1 / 16 := by
  obtain ⟨a0, a1, -⟩ := D₁_atRisk
  rw [CensoredData.greenwoodVariance_eq_naive, D₁_kmSurvival_two, D₁_filter_two,
    sum_pair (by decide), a0, a1]
  norm_num [D₁]

/-- The exponential bound at `t = 2`: `1/2 ≤ exp (-7/12)`. -/
example : (1 / 2 : ℝ) ≤ Real.exp (-(7 / 12)) := by
  simpa [D₁_kmSurvival_two, D₁_nelsonAalen_two] using D₁.kmSurvival_le_exp_neg_nelsonAalen 2

/-- The Nelson–Aalen jump at `t₁ = 2` is `d₁ / Y₁ = 1/3`. -/
example : D₁.nelsonAalen (D₁.time 1) =
    (∑ l with l < (1 : Fin 3), (D₁.deaths l : ℝ) / D₁.atRisk l) + 1 / 3 := by
  obtain ⟨-, a1, -⟩ := D₁_atRisk
  rw [D₁.nelsonAalen_time 1, a1]
  norm_num [D₁]

/-! ### Everybody at risk dies: the Greenwood domain convention -/

/-- Two subjects dying at `1` and `2`; at `2` the only subject at risk dies (`d = Y = 1`). -/
noncomputable def D₂ : CensoredData 2 where
  time := ![1, 2]
  strictMono_time := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i; norm_num
  deaths := ![1, 1]
  censored := ![0, 0]

theorem D₂_atRisk : D₂.atRisk 0 = 2 ∧ D₂.atRisk 1 = 1 := by decide

/-- `Â(2) = 1/2 + 1/1 = 3/2`. -/
theorem D₂_nelsonAalen_two : D₂.nelsonAalen 2 = 3 / 2 := by
  have hset : univ.filter (fun j : Fin 2 => D₂.time j ≤ 2) = univ := by
    ext j
    simp only [mem_filter, mem_univ, true_and, iff_true]
    fin_cases j <;> norm_num [D₂]
  obtain ⟨a0, a1⟩ := D₂_atRisk
  rw [CensoredData.nelsonAalen, hset, Fin.sum_univ_two, a0, a1]
  norm_num [D₂]

/-- The time `t₁ = 2` with `d = Y` is excluded from Greenwood's sum, and `Ŝ(2) = 0`. -/
example : D₂.kmSurvival 2 = 0 ∧ D₂.greenwoodVariance 2 = 0 := by
  have hd : (0 : ℕ) < D₂.deaths 1 := by decide
  have he : D₂.deaths 1 = D₂.atRisk 1 := by decide
  have ht : D₂.time 1 ≤ 2 := by norm_num [D₂]
  exact ⟨D₂.kmSurvival_eq_zero_of_deaths_eq_atRisk ht hd he,
    D₂.greenwoodVariance_eq_zero_of_deaths_eq_atRisk ht hd he⟩

/-! ### All observations censored -/

/-- Three subjects, all censored (one at `1`, two at `2`). -/
noncomputable def D₃ : CensoredData 2 where
  time := ![1, 2]
  strictMono_time := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    fin_cases i; norm_num
  deaths := ![0, 0]
  censored := ![1, 2]

/-- With no deaths the cumulative hazard estimate is `0` everywhere. -/
example (t : ℝ) : D₃.nelsonAalen t = 0 :=
  sum_eq_zero fun j _ => by fin_cases j <;> simp [D₃]

/-! ### The tied log-rank variance term -/

/-- One tied risk set with `Y = 4`, `Y₁ = 2`, `d = 2`: the tied (hypergeometric) variance is
`2·2·2·2 / (4²·3) = 1/3`. -/
theorem tied_four_two_two : tiedLogRankVarianceTerm 4 2 2 = 1 / 3 := by
  norm_num [tiedLogRankVarianceTerm]

/-- The Breslow information of the same two tied events is `2 · (2·2 / 4²) = 1/2`. -/
theorem breslow_four_two_two : (2 : ℝ) * (2 * (4 - 2) / 4 ^ 2) = 1 / 2 := by norm_num

/-- The tied variance `1/3` is strictly below the Breslow information `1/2`. -/
example : tiedLogRankVarianceTerm 4 2 2 < 2 * ((2 : ℝ) * ((4 : ℝ) - 2) / (4 : ℝ) ^ 2) := by
  rw [tied_four_two_two]; norm_num

/-- With a single failure (`d = 1`), `Y = 4`, `Y₁ = 2`: both equal `2·2/4² = 1/4`. -/
example : tiedLogRankVarianceTerm 4 2 1 = 1 / 4 := by
  rw [tiedLogRankVarianceTerm_one (by norm_num)]; norm_num

/-- `Y ≤ 1` is deterministic: the term vanishes. -/
example (Y₁ d : ℕ) : tiedLogRankVarianceTerm 1 Y₁ d = 0 := by
  simp [tiedLogRankVarianceTerm]

/-- Nonnegativity at a boundary case `Y₁ = Y = d`. -/
example : 0 ≤ tiedLogRankVarianceTerm 3 3 3 := tiedLogRankVarianceTerm_nonneg le_rfl le_rfl

/-! The same tied risk set in the Cox model: four subjects at risk at time `1`, two of them in
group 1, two tied events. -/

/-- Four subjects: `0, 1` fail at time `1`; `2, 3` are censored at time `2`. -/
noncomputable def T₄ : Fin 4 → ℝ := ![1, 1, 2, 2]

/-- Subjects `0` and `1` have observed events. -/
def δ₄ : Fin 4 → Bool := ![true, true, false, false]

/-- Subjects `0` and `2` are in group 1. -/
def g₄ : Fin 4 → Bool := ![true, false, true, false]

theorem riskSet_T₄_of_lt_two (i : Fin 4) (hi : T₄ i = 1) : riskSet T₄ i = univ := by
  ext l
  simp only [riskSet, mem_filter, mem_univ, true_and, iff_true, hi]
  fin_cases l <;> norm_num [T₄]

/-- **The Cox (Breslow) information of the tied risk set is `1/2`**, not the tied log-rank
variance `1/3` (`tied_four_two_two`). -/
theorem breslowInformation_T₄ : breslowInformation T₄ δ₄ g₄ = 1 / 2 := by
  have hδ : univ.filter (fun i => δ₄ i = true) = {0, 1} := by decide
  have hg : univ.filter (fun l => g₄ l = true) = {0, 2} := by decide
  rw [breslowInformation, hδ, sum_pair (by decide)]
  simp only [numAtRisk, numAtRiskIn, riskSet_T₄_of_lt_two 0 (by norm_num [T₄]),
    riskSet_T₄_of_lt_two 1 (by norm_num [T₄]), hg]
  norm_num

/-- The tied term `1/3` is the hypergeometric variance: drawing `d = 2` of `Y = 4` subjects with
`Y₁ = 2` in group 1, the mean is `1` and `P(0) = P(2) = 1/6`, so `∑ (k - 1)² P(k) = 1/3`. -/
example : tiedLogRankVarianceTerm 4 2 2 =
    ∑ k ∈ range 3, ((k : ℝ) - 2 * 2 / 4) ^ 2 * ProbabilityTheory.hypergeometricReal 4 2 2 k := by
  exact_mod_cast tiedLogRankVarianceTerm_eq_variance (Y := 4) (Y₁ := 2) (d := 2) (by norm_num)
    (by norm_num) (by norm_num)

example : ∑ k ∈ range 3, ((k : ℝ) - 1) ^ 2 * ProbabilityTheory.hypergeometricReal 4 2 2 k =
    1 / 3 := by
  norm_num [Finset.sum_range_succ, ProbabilityTheory.hypergeometricReal, Nat.choose]

#print axioms tiedLogRankVarianceTerm_eq_variance
#print axioms CensoredData.nelsonAalen_mono
#print axioms CensoredData.kmSurvival_le_exp_neg_nelsonAalen
#print axioms CensoredData.kmMass_eq_mul_nelsonAalen_jump
#print axioms CensoredData.greenwoodVariance_nonneg
#print axioms CensoredData.greenwoodVariance_eq_naive
#print axioms CensoredData.greenwoodVariance_eq_zero_of_deaths_eq_atRisk
#print axioms tiedLogRankVarianceTerm_nonneg
#print axioms tiedLogRankVarianceTerm_one
#print axioms tiedLogRankVarianceTerm_le

end MathlibExtTest.Probability.Statistics.NelsonAalen
