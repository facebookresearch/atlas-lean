/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.LeftTruncation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

@[expose] public section

open MeasureTheory Finset
open scoped ENNReal NNReal ProbabilityTheory
open MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.LeftTruncation
open MathlibExt.Probability.Statistics.Censoring

namespace MathlibExtTest.Probability.Statistics.LeftTruncation

/-- Four grid times `1 < 2 < 3 < 4`. -/
noncomputable def t : Fin 4 → ℝ := ![1, 2, 3, 4]

theorem t_strictMono : StrictMono t := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i <;> norm_num [t]

/-! ### The entry convention -/

/-- An entry at `L = 2 = t₁` has entry index `1`: the subject is not at risk at `t₁`. -/
example : ¬ entryIndex t 2 < (1 : Fin 4) := by
  rw [entryIndex_lt_iff t_strictMono]; norm_num [t]

/-- ... but it is at risk at `t₂`. -/
example : entryIndex t 2 < (2 : Fin 4) := by
  rw [entryIndex_lt_iff t_strictMono]; norm_num [t]

/-- An entry before the first grid time precedes every grid index. -/
example (j : Fin 4) : entryIndex t (1 / 2) < j := by
  rw [entryIndex_lt_iff t_strictMono]
  fin_cases j <;> norm_num [t]

/-! ### No subjects -/

/-- The empty sample. -/
noncomputable def D₀ : DelayedEntryData 4 0 where
  time := t
  strictMono_time := t_strictMono
  entry := Fin.elim0
  exit := Fin.elim0
  event := Fin.elim0
  entry_lt_exit i := i.elim0

example (j : Fin 4) : D₀.atRisk j = 0 ∧ D₀.deaths j = 0 ∧ D₀.censored j = 0 := by
  simp [DelayedEntryData.atRisk, DelayedEntryData.deaths, DelayedEntryData.censored]

example : D₀.support = ∅ := by
  ext j; simp [DelayedEntryData.mem_support, DelayedEntryData.atRisk]

example (s : ℝ) : D₀.plSurvival s = 1 ∧ D₀.nelsonAalen s = 0 := by
  have : D₀.support = ∅ := by
    ext j; simp [DelayedEntryData.mem_support, DelayedEntryData.atRisk]
  simp [DelayedEntryData.plSurvival, DelayedEntryData.nelsonAalen, this]

/-! ### Delayed entries with changing risk sets -/

/-- Five subjects on the grid `1 < 2 < 3 < 4`:
* subject 0 enters before `t₀` and dies at `t₀`;
* subject 1 enters before `t₀` and is censored at `t₂`;
* subject 2 enters in `[t₀, t₁)` and dies at `t₁`;
* subject 3 enters exactly at `t₁` (not at risk there) and dies at `t₃`;
* subject 4 enters exactly at `t₁`, the time subject 2 dies, and dies at `t₂`. -/
noncomputable def D : DelayedEntryData 4 5 where
  time := t
  strictMono_time := t_strictMono
  entry := ![⊥, ⊥, (0 : Fin 4), (1 : Fin 4), (1 : Fin 4)]
  exit := ![0, 2, 1, 3, 2]
  event := ![true, false, true, true, true]
  entry_lt_exit := by decide

/-- Numbers at risk `Yⱼ = #{entryᵢ < j ≤ exitᵢ} = 2, 2, 3, 1`. At `t₁` subjects 3 and 4, who
enter exactly at `t₁`, are not counted. -/
theorem D_atRisk : D.atRisk = ![2, 2, 3, 1] := by
  funext j; fin_cases j <;> decide

theorem D_deaths : D.deaths = ![1, 1, 1, 1] := by
  funext j; fin_cases j <;> decide

theorem D_censored : D.censored = ![0, 0, 1, 0] := by
  funext j; fin_cases j <;> decide

/-- The entered-minus-exited identity at `t₂`: `Y₂ + #{exit < 2} = #{entry < 2}`, i.e.
`3 + 2 = 5`. -/
example : D.atRisk 2 + #{i | D.exit i < 2} = #{i | D.entry i < (2 : Fin 4)} :=
  D.atRisk_add_card_exit_lt 2

example : #{i | D.exit i < 2} = 2 ∧ #{i | D.entry i < (2 : Fin 4)} = 5 := by decide

/-- The untruncated numbers at risk, ignoring entries, are `5, 4, 3, 1`. -/
theorem D_atRisk_toCensoredData :
    D.toCensoredData.atRisk 0 = 5 ∧ D.toCensoredData.atRisk 1 = 4 := by
  simp only [DelayedEntryData.toCensoredData, CensoredData.atRisk_ofSubjects]
  decide

/-- The delayed-entry product-limit estimate at `t = 3`: `(1 - 1/2)(1 - 1/2)(1 - 1/3) = 1/6`. -/
theorem D_plSurvival : D.plSurvival 3 = 1 / 6 := by
  rw [DelayedEntryData.plSurvival_eq_prod_all, prod_filter, Fin.prod_univ_four]
  simp only [DelayedEntryData.plFactor, DelayedEntryData.hazardEst, D_atRisk, D_deaths]
  norm_num [D, t]

/-- Ignoring delayed entry gives the naive Kaplan–Meier value `(1 - 1/5)(1 - 1/4)(1 - 1/3) = 2/5`
at `t = 3`, not `1/6`: the reduction to Kaplan–Meier needs its early-entry hypothesis. -/
theorem D_kmSurvival_toCensoredData : D.toCensoredData.kmSurvival 3 = 2 / 5 := by
  have hY : D.toCensoredData.atRisk = ![5, 4, 3, 1] := by
    funext j
    simp only [DelayedEntryData.toCensoredData, CensoredData.atRisk_ofSubjects]
    fin_cases j <;> decide
  rw [CensoredData.kmSurvival, prod_filter, Fin.prod_univ_four]
  simp only [CensoredData.kmFactor, hY, DelayedEntryData.deaths_toCensoredData, D_deaths]
  norm_num [DelayedEntryData.toCensoredData, D, t]

example : ¬ D.EntriesPrecedeExits := fun h => absurd (h 3 0) (by decide)

/-- `D` is gap-free (somebody is at risk at every grid time), so telescoping applies. -/
theorem D_gapFree : D.GapFree := fun _ j _ _ _ _ _ => by
  simp only [DelayedEntryData.mem_support, D_atRisk]
  fin_cases j <;> decide

example : ∑ j ∈ D.support with D.time j ≤ 3, D.plMass j + D.plSurvival 3 = 1 :=
  D.sum_plMass_add_plSurvival D_gapFree 3

/-! ### A zero-risk gap -/

/-- Two subjects: subject 0 enters before `t₀` and is censored at `t₀`; subject 1 enters at `t₁`
and dies at `t₃`. Nobody is at risk at `t₁`. -/
noncomputable def G : DelayedEntryData 4 2 where
  time := t
  strictMono_time := t_strictMono
  entry := ![⊥, (1 : Fin 4)]
  exit := ![0, 3]
  event := ![false, true]
  entry_lt_exit := by decide

theorem G_atRisk : G.atRisk = ![1, 0, 1, 1] := by
  funext j; fin_cases j <;> decide

/-- The gap time `t₁` is outside the support and has no events, while `t₂` is supported. -/
example : (1 : Fin 4) ∉ G.support ∧ (2 : Fin 4) ∈ G.support ∧ G.deaths 1 = 0 := by
  simp only [DelayedEntryData.mem_support, G_atRisk]
  refine ⟨by decide, by decide, by decide⟩

/-- The gap makes `G` fail `GapFree`, so the telescoping theorem does not apply to it. -/
example : ¬ G.GapFree := fun h => by
  have := h (i := 0) (j := 1) (l := 2) (by decide) (by decide)
    (by simp [DelayedEntryData.mem_support, G_atRisk])
    (by simp [DelayedEntryData.mem_support, G_atRisk])
  simp [DelayedEntryData.mem_support, G_atRisk] at this

/-! ### Regression probe: a gap between two supported stretches -/

/-- Three subjects: subjects 0 and 1 enter before `t₀` and leave at `t₀` (one death, one
censoring); subject 2 enters at `t₁` and dies at `t₂`. Numbers at risk `2, 0, 1, 0`: two
supported stretches `{t₀}` and `{t₂}` separated by a gap at `t₁`. -/
noncomputable def P : DelayedEntryData 4 3 where
  time := t
  strictMono_time := t_strictMono
  entry := ![⊥, ⊥, (1 : Fin 4)]
  exit := ![0, 0, 2]
  event := ![true, false, true]
  entry_lt_exit := by decide

theorem P_atRisk : P.atRisk = ![2, 0, 1, 0] := by
  funext j; fin_cases j <;> decide

theorem P_deaths : P.deaths = ![1, 0, 1, 0] := by
  funext j; fin_cases j <;> decide

/-- `P` is not gap-free: `t₀` and `t₂` are supported, `t₁` is not. -/
theorem P_not_gapFree : ¬ P.GapFree := fun h => by
  have := h (i := 0) (j := 1) (l := 2) (by decide) (by decide)
    (by simp [DelayedEntryData.mem_support, P_atRisk])
    (by simp [DelayedEntryData.mem_support, P_atRisk])
  simp [DelayedEntryData.mem_support, P_atRisk] at this

/-- The totalized values still exist: `Ŝ(2) = 1/2` inside the gap, and the jump at `t₂`, where
the only subject at risk dies, is `1/2`. Neither is a survival quantity: the death at `t₂` is
certain given entry, and the factor `1/2` comes from the stretch before the gap. Because
`P_not_gapFree`, `sum_plMass_add_plSurvival` does not apply to `P`. -/
example : P.plSurvival 2 = 1 / 2 ∧ P.plMass 2 = 1 / 2 := by
  have hs : P.support = {0, 2} := by
    ext j; fin_cases j <;> simp [DelayedEntryData.mem_support, P_atRisk]
  refine ⟨?_, ?_⟩
  · rw [DelayedEntryData.plSurvival_eq_prod_all, prod_filter, Fin.prod_univ_four]
    simp only [DelayedEntryData.plFactor, DelayedEntryData.hazardEst, P_atRisk, P_deaths]
    norm_num [P, t]
  · have hf : ({0, 2} : Finset (Fin 4)).filter (· < 2) = {0} := by decide
    rw [DelayedEntryData.plMass, hs, hf]
    simp only [DelayedEntryData.plFactor, DelayedEntryData.hazardEst, P_atRisk, P_deaths]
    norm_num

/-! ### Early entry: reduction to Kaplan–Meier -/

/-- Three subjects on `1 < 2 < 3 < 4`; entries at index `0`, `0`, `⊥`, every one before the first
exit time `t₁`. At `t₀` the delayed-entry number at risk (`1`) differs from the untruncated one
(`3`), but nobody leaves at `t₀`. -/
noncomputable def E : DelayedEntryData 4 3 where
  time := t
  strictMono_time := t_strictMono
  entry := ![(0 : Fin 4), (0 : Fin 4), ⊥]
  exit := ![1, 2, 1]
  event := ![true, true, false]
  entry_lt_exit := by decide

theorem E_entriesPrecedeExits : E.EntriesPrecedeExits := by
  unfold DelayedEntryData.EntriesPrecedeExits; decide

/-- Early entry discharges `GapFree`, although `E` has nobody at risk at `t₃` (after the last
exit). -/
example : E.GapFree := DelayedEntryData.gapFree_of_entriesPrecedeExits E_entriesPrecedeExits

example : E.atRisk 0 = 1 ∧ E.toCensoredData.atRisk 0 = 3 := by
  simp only [DelayedEntryData.toCensoredData, CensoredData.atRisk_ofSubjects]
  decide

/-- The explicit untruncated grouped data: deaths `0, 1, 1, 0`, censorings `0, 1, 0, 0`. -/
noncomputable def E' : CensoredData 4 where
  time := t
  strictMono_time := t_strictMono
  deaths := ![0, 1, 1, 0]
  censored := ![0, 1, 0, 0]

theorem E_toCensoredData : E.toCensoredData = E' := by
  simp only [DelayedEntryData.toCensoredData, CensoredData.ofSubjects, E']
  congr 1 <;> funext j <;> fin_cases j <;> decide

/-- The reduction: the delayed-entry product-limit estimate equals Kaplan–Meier of `E'`. -/
example (s : ℝ) : E.plSurvival s = E'.kmSurvival s := by
  rw [DelayedEntryData.plSurvival_eq_kmSurvival E_entriesPrecedeExits, E_toCensoredData]

example (s : ℝ) : E.nelsonAalen s = E'.nelsonAalen s := by
  rw [DelayedEntryData.nelsonAalen_eq_nelsonAalen E_entriesPrecedeExits, E_toCensoredData]

/-- The Kaplan–Meier value at `t = 3`: `(1 - 1/3)(1 - 1/1) = 0`; at `t = 2`: `2/3`. -/
example : E.plSurvival 2 = 2 / 3 := by
  rw [DelayedEntryData.plSurvival_eq_kmSurvival E_entriesPrecedeExits, E_toCensoredData]
  have hY : E'.atRisk = ![3, 3, 1, 0] := by
    funext j; fin_cases j <;> simp [CensoredData.atRisk, E', Finset.sum_filter, Fin.sum_univ_four]
  rw [CensoredData.kmSurvival, prod_filter, Fin.prod_univ_four]
  simp only [CensoredData.kmFactor, hY]
  norm_num [E', t]

/-! ### Identification under independent truncation -/

/-- Event-time law `P(T = 0, 1, 2) = 1/4, 1/4, 1/2`. -/
noncomputable def pT : PMF (Fin 3) :=
  PMF.ofFintype (fun i => ((![1 / 4, 1 / 4, 1 / 2] : Fin 3 → ℝ≥0) i : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one, Fin.sum_univ_three]
    norm_num)

/-- Censoring-time law, uniform on `Fin 3`. -/
noncomputable def pC : PMF (Fin 3) :=
  PMF.ofFintype (fun _ => ((1 / 3 : ℝ≥0) : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one, Fin.sum_univ_three]
    norm_num)

/-- Entry-time law `P(L = 0, 1, 2) = 1/2, 1/2, 0`. -/
noncomputable def pL : PMF (Fin 3) :=
  PMF.ofFintype (fun i => ((![1 / 2, 1 / 2, 0] : Fin 3 → ℝ≥0) i : ℝ≥0∞)) (by
    rw [← ENNReal.ofNNReal_finsetSum, ENNReal.coe_eq_one, Fin.sum_univ_three]
    norm_num)

/-- Nothing is identified at the first grid point: `P(L < 0) = 0`. -/
example : truncAtRiskMass (indepTruncLaw pT pC pL) 0 = 0 := by
  rw [truncAtRiskMass_indepTruncLaw, entryMass]
  simp

theorem entryMass_pL_one : entryMass pL 1 = 1 / 2 := by
  have : {l : Fin 3 | l < 1} = {0} := by ext l; fin_cases l <;> simp
  rw [entryMass, this, measureReal_singleton]
  simp [pL]

theorem survivalMass_pT_one : survivalMass pT 1 = 3 / 4 := by
  simp only [survivalMass_eq_sum]
  simp [Finset.sum_filter, Fin.sum_univ_three, pT]
  norm_num

theorem survivalMass_pC_one : survivalMass pC 1 = 2 / 3 := by
  rw [survivalMass_eq_sum, Finset.sum_filter, Fin.sum_univ_three]
  simp [pC]
  norm_num

/-- At `j = 1` the at-risk mass is `3/4 · 2/3 · 1/2 = 1/4 ≠ 0`, and the observed ratio among
included subjects is the hazard `P(T = 1) / P(T ≥ 1) = (1/4) / (3/4) = 1/3`. -/
example :
    truncEventMass ((indepTruncLaw pT pC pL)[|inclusion]) 1 /
        truncAtRiskMass ((indepTruncLaw pT pC pL)[|inclusion]) 1 = 1 / 3 := by
  have hR : truncAtRiskMass (indepTruncLaw pT pC pL) 1 = 1 / 4 := by
    rw [truncAtRiskMass_indepTruncLaw, survivalMass_pT_one, survivalMass_pC_one,
      entryMass_pL_one]
    norm_num
  rw [truncEventMass_div_truncAtRiskMass_cond pT pC pL 1 (by rw [hR]; norm_num), hazard,
    survivalMass_pT_one]
  simp [pT]
  norm_num

end MathlibExtTest.Probability.Statistics.LeftTruncation
