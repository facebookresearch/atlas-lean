/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.Data

@[expose] public section

open Finset
open MathlibExt.Probability.Statistics.KaplanMeier
open MathlibExt.Probability.Statistics.CompetingRisks
open MathlibExt.Probability.Statistics.CoxPartialLikelihood

namespace MathlibExtTest.Probability.Statistics.SurvivalData

/-- Three observation times `1 < 2 < 3`. -/
noncomputable def t : Fin 3 → ℝ := ![1, 2, 3]

theorem t_strictMono : StrictMono t := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i <;> norm_num [t]

/-- Five subjects: two tied at `t₀` (one event, one censored), nobody at `t₁`, three tied at
`t₂` (two events, one censored). -/
def g : Fin 5 → Fin 3 := ![0, 0, 2, 2, 2]

/-- Event flags of the five subjects. -/
def δ : Fin 5 → Bool := ![true, false, true, true, false]

/-- The grouped data of the five subjects. -/
noncomputable def D : CensoredData 3 := CensoredData.ofSubjects t t_strictMono g δ

/-- The hand-written grouped data: deaths `1, 0, 2`, censorings `1, 0, 1`. -/
noncomputable def D' : CensoredData 3 where
  time := t
  strictMono_time := t_strictMono
  deaths := ![1, 0, 2]
  censored := ![1, 0, 1]

/-- The subject-level construction gives exactly the hand-written grouped data. -/
theorem D_eq : D = D' := by
  simp only [D, D', CensoredData.ofSubjects]
  congr 1 <;> funext j <;> fin_cases j <;> decide

/-! ### Ground truth from the definitions

The checks in this section unfold `size`, `atRisk`, `riskSet`, `numAtRisk`, `totalEvents` and
`toCensoredData` directly; none of them uses a theorem of `Survival.Data`. -/

theorem D_size : D.size = 5 := by decide

theorem D_atRisk : D.atRisk 0 = 5 ∧ D.atRisk 1 = 3 ∧ D.atRisk 2 = 3 := by decide

/-- The empty time `t₁` has no deaths and no censorings. -/
example : D.deaths 1 = 0 ∧ D.censored 1 = 0 := by decide

/-- Fiber split at the tied time `t₂`: `2 + 1 = 3` subjects. -/
example : D.deaths 2 + D.censored 2 = 3 := by decide

/-- The Cox risk set of subject `2` (time `3`) is `{2, 3, 4}`. -/
theorem riskSet_two : riskSet (t ∘ g) 2 = {2, 3, 4} := by
  ext l
  rw [riskSet, mem_filter]
  fin_cases l <;> norm_num [t, g]

/-- The Cox risk set of subject `1` (time `1`) is everyone. -/
theorem riskSet_one : riskSet (t ∘ g) 1 = univ := by
  ext l
  rw [riskSet, mem_filter]
  fin_cases l <;> norm_num [t, g]

/-- Cox spot-check from the definitions: risk-set sizes `3` and `5`. -/
theorem numAtRisk_fixture : numAtRisk (t ∘ g) 2 = 3 ∧ numAtRisk (t ∘ g) 1 = 5 := by
  rw [numAtRisk, numAtRisk, riskSet_two, riskSet_one]
  decide

/-- Swapping subjects `0` and `2` (different times) leaves the grouped counts unchanged. -/
theorem swap_eq : CensoredData.ofSubjects t t_strictMono (g ∘ Equiv.swap 0 2)
    (δ ∘ Equiv.swap 0 2) = D' := by
  simp only [D', CensoredData.ofSubjects]
  congr 1 <;> funext j <;> fin_cases j <;> decide

/-- The swap really reorders the subjects. -/
example : g ∘ Equiv.swap 0 2 ≠ g := fun h => by
  have := congrFun h 0
  revert this
  decide

/-- No subjects: size `0` and nobody at risk. -/
example : (CensoredData.ofSubjects t t_strictMono (Fin.elim0 : Fin 0 → Fin 3) Fin.elim0).size = 0 ∧
    (CensoredData.ofSubjects t t_strictMono (Fin.elim0 : Fin 0 → Fin 3) Fin.elim0).atRisk 0 = 0 :=
  by decide

/-- All subjects censored: no deaths at any time, everyone still counted at risk. -/
example (j : Fin 3) : (CensoredData.ofSubjects t t_strictMono g fun _ => false).deaths j = 0 ∧
    (CensoredData.ofSubjects t t_strictMono g fun _ => false).atRisk 0 = 5 := by
  fin_cases j <;> decide

/-- Causes of the five subjects among `2` competing risks (`none` = censored). -/
def cause : Fin 5 → Option (Fin 2) := ![some 0, none, some 1, some 0, none]

/-- Subject-level competing-risks data: one cause-`0` and one cause-`1` failure at `t₂`. -/
example : (CompetingRiskData.ofSubjects t t_strictMono g cause).events 2 0 = 1 ∧
    (CompetingRiskData.ofSubjects t t_strictMono g cause).events 2 1 = 1 := by decide

/-- Forgetting causes recovers `D'`, by unfolding `toCensoredData` and `totalEvents`. -/
theorem competing_toCensoredData :
    (CompetingRiskData.ofSubjects t t_strictMono g cause).toCensoredData = D' := by
  simp only [CompetingRiskData.toCensoredData, D']
  congr 1 <;> funext j <;> fin_cases j <;> decide

/-! ### The bridge theorems on the fixture

These apply the theorems of `Survival.Data` and agree with the ground truth above. -/

example : D.size = 5 := CensoredData.size_ofSubjects ..

example : D.atRisk 2 = #{i | (2 : Fin 3) ≤ g i} := CensoredData.atRisk_ofSubjects ..

example : D.deaths 2 + D.censored 2 = #{i | g i = 2} :=
  CensoredData.deaths_add_censored_ofSubjects ..

example : D.deaths 1 = 0 ∧ D.censored 1 = 0 :=
  CensoredData.deaths_ofSubjects_eq_zero_and_censored_ofSubjects_eq_zero _ _ _ _ (by decide)

/-- The risk-set bridge gives subject `2` the risk set `{2, 3, 4}` (subjects recorded at `t₂`). -/
example : riskSet (t ∘ g) 2 = {2, 3, 4} :=
  (riskSet_comp_group t_strictMono g 2).trans (by decide)

/-- The Cox bridge reproduces the directly computed risk-set size. -/
example : numAtRisk (t ∘ g) 2 = D.atRisk 2 := numAtRisk_comp_group t_strictMono g δ 2

example : CensoredData.ofSubjects t t_strictMono (g ∘ Equiv.swap 0 2) (δ ∘ Equiv.swap 0 2) = D :=
  CensoredData.ofSubjects_comp_equiv ..

example : (CompetingRiskData.ofSubjects t t_strictMono g cause).toCensoredData = D := by
  rw [CompetingRiskData.toCensoredData_ofSubjects, D]
  congr 1
  funext i
  fin_cases i <;> rfl

end MathlibExtTest.Probability.Statistics.SurvivalData
