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

theorem D_size : D.size = 5 := CensoredData.size_ofSubjects ..

theorem D_atRisk : D.atRisk 0 = 5 ∧ D.atRisk 1 = 3 ∧ D.atRisk 2 = 3 := by
  simp only [D, CensoredData.atRisk_ofSubjects]
  decide

/-- The empty time `t₁` has no deaths and no censorings. -/
example : D.deaths 1 = 0 ∧ D.censored 1 = 0 :=
  CensoredData.deaths_ofSubjects_eq_zero_and_censored_ofSubjects_eq_zero _ _ _ _
    (by decide)

/-- Fiber split at the tied time `t₂`: `2 + 1 = 3` subjects. -/
example : D.deaths 2 + D.censored 2 = 3 := by
  rw [D, CensoredData.deaths_add_censored_ofSubjects]
  decide

/-- Cox spot-check: subject `2` (time `3`) has risk set of size `3`, subject `1` (time `1`) of
size `5`. -/
example : numAtRisk (t ∘ g) 2 = 3 ∧ numAtRisk (t ∘ g) 1 = 5 := by
  rw [numAtRisk_comp_group t_strictMono g δ, numAtRisk_comp_group t_strictMono g δ]
  exact ⟨D_atRisk.2.2, D_atRisk.1⟩

/-- Swapping subjects `0` and `2` (different times) leaves the grouped data unchanged. -/
example : CensoredData.ofSubjects t t_strictMono (g ∘ Equiv.swap 0 2) (δ ∘ Equiv.swap 0 2) = D' :=
  (CensoredData.ofSubjects_comp_equiv ..).trans D_eq

/-- The swap really reorders the subjects. -/
example : g ∘ Equiv.swap 0 2 ≠ g := fun h => by
  have := congrFun h 0
  revert this
  decide

/-- No subjects: size `0` and nobody at risk. -/
example : (CensoredData.ofSubjects t t_strictMono (Fin.elim0 : Fin 0 → Fin 3) Fin.elim0).size = 0 ∧
    (CensoredData.ofSubjects t t_strictMono (Fin.elim0 : Fin 0 → Fin 3) Fin.elim0).atRisk 0 = 0 :=
  ⟨CensoredData.size_ofSubjects .., by simp [CensoredData.atRisk_ofSubjects]⟩

/-- All subjects censored: no deaths at any time, everyone still counted at risk. -/
example (j : Fin 3) : (CensoredData.ofSubjects t t_strictMono g fun _ => false).deaths j = 0 ∧
    (CensoredData.ofSubjects t t_strictMono g fun _ => false).atRisk 0 = 5 := by
  simp only [CensoredData.ofSubjects_deaths, CensoredData.atRisk_ofSubjects]
  exact ⟨by simp, by decide⟩

/-- Causes of the five subjects among `2` competing risks (`none` = censored). -/
def cause : Fin 5 → Option (Fin 2) := ![some 0, none, some 1, some 0, none]

/-- Subject-level competing-risks data: one cause-`0` and one cause-`1` failure at `t₂`, and
forgetting causes recovers `D'`. -/
example : (CompetingRiskData.ofSubjects t t_strictMono g cause).events 2 0 = 1 ∧
    (CompetingRiskData.ofSubjects t t_strictMono g cause).events 2 1 = 1 ∧
    (CompetingRiskData.ofSubjects t t_strictMono g cause).toCensoredData = D' := by
  refine ⟨by decide, by decide, ?_⟩
  rw [CompetingRiskData.toCensoredData_ofSubjects, ← D_eq, D]
  congr 1
  funext i
  fin_cases i <;> rfl

end MathlibExtTest.Probability.Statistics.SurvivalData
