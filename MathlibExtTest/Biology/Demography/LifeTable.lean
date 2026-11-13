/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.Demography.LifeTable
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation

import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

/-!
# Life-table examples: worked computations

Concrete populations exercising the `LifeTable` API: cohort accounting,
death probabilities, survival products, extinction, open populations,
person-years non-identification, same-rates composition effects with the
`directlyStandardizedRate` link, the Kitagawa decomposition,
single-standard interaction, crude death rates, the `centerMass` and
standardization bridges, valid-population bounds, and boundary exclusion
for signed, zero, and empty populations. Each focused test applies the
corresponding public theorem and discharges its hypotheses.
-/

@[expose] public section

namespace MathlibExtTest.Biology.Demography.LifeTable

open MathlibExt.Biology.Demography.LifeTable

/-- Example survivors `(1000, 900, 720, 360)` then `360`. -/
def exampleL : ℕ → ℝ
  | 0 => 1000
  | 1 => 900
  | 2 => 720
  | _ => 360

/-- Example deaths `(100, 180, 360)` then `0`. -/
def exampleD : ℕ → ℝ
  | 0 => 100
  | 1 => 180
  | 2 => 360
  | _ => 0

/-- Closed accounting holds at every age for the example. -/
theorem example_step : ∀ x, exampleL (x + 1) = exampleL x - exampleD x := by
  intro x
  match x with
  | 0 => norm_num [exampleL, exampleD]
  | 1 => norm_num [exampleL, exampleD]
  | 2 => norm_num [exampleL, exampleD]
  | n + 3 => norm_num [exampleL, exampleD]

/-- Death probabilities at ages `0, 1, 2` are `1/10, 1/5, 1/2`. -/
theorem example_deathProbability :
    deathProbability exampleL exampleD 0 (by norm_num [exampleL]) = 1 / 10 ∧
    deathProbability exampleL exampleD 1 (by norm_num [exampleL]) = 1 / 5 ∧
    deathProbability exampleL exampleD 2 (by norm_num [exampleL]) = 1 / 2 := by
  unfold deathProbability
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [exampleL, exampleD]

/-- Survivors at age `3` via the survival product `survivors_eq_mul_prod`. -/
theorem example_survival_product :
    exampleL 3 = 1000 * ((1 - 1 / 10) * (1 - 1 / 5) * (1 - 1 / 2)) := by
  have hpos : ∀ k : Fin 3, 0 < exampleL k := by
    intro k
    fin_cases k <;> norm_num [exampleL]
  rw [survivors_eq_mul_prod exampleL exampleD example_step 3 hpos, Fin.prod_univ_three]
  norm_num [deathProbability, exampleL, exampleD]

/-- Extinct survivors `(3, 2, 0)` then `0`. -/
def extinctL : ℕ → ℝ
  | 0 => 3
  | 1 => 2
  | _ => 0

/-- Extinct deaths `(1, 2)` then `0`. -/
def extinctD : ℕ → ℝ
  | 0 => 1
  | 1 => 2
  | _ => 0

/-- Closed accounting holds at every age for the extinct cohort. -/
theorem extinct_step : ∀ t, extinctL (t + 1) = extinctL t - extinctD t := by
  intro t
  match t with
  | 0 => norm_num [extinctL, extinctD]
  | 1 => norm_num [extinctL, extinctD]
  | n + 2 => norm_num [extinctL, extinctD]

/-- Initial size `1 + 2` from the extinct cohort, via `extinct_cohort`. -/
theorem example_extinct_cohort : extinctL 0 = 1 + 2 := by
  rw [extinct_cohort extinctL extinctD extinct_step (T := 2) (by norm_num [extinctL])]
  norm_num [Finset.sum_range_succ, extinctD]

/-- Zero survivors `(10, 4, 0)` then `0`. -/
def zeroL : ℕ → ℝ
  | 0 => 10
  | 1 => 4
  | _ => 0

/-- Zero deaths `(6, 4)` then `0`. -/
def zeroD : ℕ → ℝ
  | 0 => 6
  | 1 => 4
  | _ => 0

/-- No positive risk set at age `2`. -/
theorem zero_survivors_no_risk_set : ¬ (0 < zeroL 2) := by
  simp [zeroL]

/-- Closed accounting holds at every age for the zero-survivor cohort. -/
theorem zero_step : ∀ x, zeroL (x + 1) = zeroL x - zeroD x := by
  intro x
  match x with
  | 0 => norm_num [zeroL, zeroD]
  | 1 => norm_num [zeroL, zeroD]
  | n + 2 => norm_num [zeroL, zeroD]

/-- Extinct cohort stays at zero, from `survivors_eq_zero_of_le`. -/
theorem zero_survivors_stay_zero : zeroL 5 = 0 := by
  refine survivors_eq_zero_of_le zeroL zeroD zero_step (fun x => ?_) (fun x => ?_)
    (k := 2) (by norm_num [zeroL]) (by norm_num)
  · match x with
    | 0 => norm_num [zeroD]
    | 1 => norm_num [zeroD]
    | n + 2 => norm_num [zeroD]
  · match x with
    | 0 => norm_num [zeroL, zeroD]
    | 1 => norm_num [zeroL, zeroD]
    | n + 2 => norm_num [zeroL, zeroD]

/-- Open sizes `10` then `9`. -/
def openP : ℕ → ℝ
  | 0 => 10
  | _ => 9

/-- Open deaths `2` then `0`. -/
def openD : ℕ → ℝ
  | 0 => 2
  | _ => 0

/-- Open net migration `1` then `0`. -/
def openM : ℕ → ℝ
  | 0 => 1
  | _ => 0

/-- Open accounting holds at every year. -/
theorem open_step : ∀ t, openP (t + 1) = openP t - openD t + openM t := by
  intro t
  match t with
  | 0 => norm_num [openP, openD, openM]
  | n + 1 => norm_num [openP, openD, openM]

/-- Open balance holds at `T = 1`, via `cohort_balance`. -/
theorem open_cohort_balance :
    openP 1 = openP 0 - ∑ t ∈ Finset.range 1, openD t + ∑ t ∈ Finset.range 1, openM t :=
  cohort_balance openP openD openM open_step 1

/-- Open population is not closed. -/
theorem open_cohort_not_closed : openP 1 ≠ openP 0 - openD 0 := by
  norm_num [openP, openD]

/-- Open population does not follow the closed product. -/
theorem open_cohort_not_product :
    openP 1 ≠ openP 0 * (1 - deathProbability openP openD 0 (by norm_num [openP])) := by
  unfold deathProbability
  norm_num [openP, openD]

/-- Person survivors `2` then `1`. -/
def personL : ℕ → ℝ
  | 0 => 2
  | _ => 1

/-- Person deaths `1` then `0`. -/
def personD : ℕ → ℝ
  | 0 => 1
  | _ => 0

/-- Same endpoints but different central rates `10/19` versus `5/6`. -/
theorem person_years_not_determined :
    personL 0 = 2 ∧ personL 1 = 1 ∧ personD 0 = 1 ∧
    centralDeathRate (personD 0) (19 / 10) (by norm_num) = 10 / 19 ∧
    centralDeathRate (personD 0) (6 / 5) (by norm_num) = 5 / 6 ∧
    centralDeathRate (personD 0) (19 / 10) (by norm_num) ≠
    centralDeathRate (personD 0) (6 / 5) (by norm_num) := by
  unfold centralDeathRate
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [personL, personD]

/-- Age-specific rates `(1/100, 1/10)` for the same-rates group. -/
noncomputable def sameRatesT : Fin 2 → ℝ := ![1 / 100, 1 / 10]

/-- Sizes `(80, 20)` for population A. -/
def sameRatesNA : Fin 2 → ℝ := ![80, 20]

/-- Sizes `(20, 80)` for population B. -/
def sameRatesNB : Fin 2 → ℝ := ![20, 80]

/-- Standard sizes `(50, 50)`. -/
def sameRatesS : Fin 2 → ℝ := ![50, 50]

/-- Same rates but crude rates `7/250` vs `41/500` differ. -/
theorem same_rates_crude_differ :
    crudeRate sameRatesNA sameRatesT = 7 / 250 ∧
    crudeRate sameRatesNB sameRatesT = 41 / 500 ∧
    crudeRate sameRatesNA sameRatesT ≠ crudeRate sameRatesNB sameRatesT := by
  have hA : crudeRate sameRatesNA sameRatesT = 7 / 250 := by
    simp [crudeRate, Fin.sum_univ_two, sameRatesNA, sameRatesT]
    norm_num
  have hB : crudeRate sameRatesNB sameRatesT = 41 / 500 := by
    simp [crudeRate, Fin.sum_univ_two, sameRatesNB, sameRatesT]
    norm_num
  exact ⟨hA, hB, by rw [hA, hB]; norm_num⟩

/-- Fixed standard `(50, 50)` gives `11/200` (populations' own compositions play no role). -/
theorem same_rates_standardized_equal :
    directlyStandardizedRate sameRatesS sameRatesT = 11 / 200 := by
  simp [directlyStandardizedRate, populationShare, Fin.sum_univ_two, sameRatesS, sameRatesT]
  norm_num

/-- Crude-rate difference is purely compositional: `27/500`. -/
theorem same_rates_difference_is_compositional :
    crudeRate sameRatesNB sameRatesT - crudeRate sameRatesNA sameRatesT = 27 / 500 ∧
    (∑ i, sameRatesT i * (populationShare sameRatesNB i - populationShare sameRatesNA i)) =
      27 / 500 ∧
    crudeRate sameRatesNB sameRatesT - crudeRate sameRatesNA sameRatesT =
      ∑ i, sameRatesT i * (populationShare sameRatesNB i - populationShare sameRatesNA i) ∧
    0 < crudeRate sameRatesNA sameRatesT ∧
    0 < crudeRate sameRatesNB sameRatesT := by
  have hA : crudeRate sameRatesNA sameRatesT = 7 / 250 := by
    simp [crudeRate, Fin.sum_univ_two, sameRatesNA, sameRatesT]
    norm_num
  have hB : crudeRate sameRatesNB sameRatesT = 41 / 500 := by
    simp [crudeRate, Fin.sum_univ_two, sameRatesNB, sameRatesT]
    norm_num
  have hS : (∑ i, sameRatesT i * (populationShare sameRatesNB i - populationShare sameRatesNA i)) =
      27 / 500 := by
    simp [populationShare, Fin.sum_univ_two, sameRatesNA, sameRatesNB, sameRatesT]
    norm_num
  have hdiff : crudeRate sameRatesNB sameRatesT - crudeRate sameRatesNA sameRatesT = 27 / 500 := by
    rw [hA, hB]
    norm_num
  have hposA : 0 < crudeRate sameRatesNA sameRatesT := by
    rw [hA]
    norm_num
  have hposB : 0 < crudeRate sameRatesNB sameRatesT := by
    rw [hB]
    norm_num
  exact ⟨hdiff, hS, (crudeRate_sub_crudeRate_of_same_rates sameRatesNA sameRatesNB sameRatesT).1,
    hposA, hposB⟩

/-- Composition effect as a DSR difference: `27/500` for the same-rates pair. -/
theorem same_rates_dsr_compositional_link :
    directlyStandardizedRate sameRatesNB sameRatesT -
        directlyStandardizedRate sameRatesNA sameRatesT = 27 / 500 ∧
    crudeRate sameRatesNB sameRatesT - crudeRate sameRatesNA sameRatesT =
      directlyStandardizedRate sameRatesNB sameRatesT -
        directlyStandardizedRate sameRatesNA sameRatesT ∧
    (∑ i, sameRatesT i * (populationShare sameRatesNB i - populationShare sameRatesNA i)) =
      directlyStandardizedRate sameRatesNB sameRatesT -
        directlyStandardizedRate sameRatesNA sameRatesT := by
  have hA : crudeRate sameRatesNA sameRatesT = 7 / 250 := by
    simp [crudeRate, Fin.sum_univ_two, sameRatesNA, sameRatesT]
    norm_num
  have hB : crudeRate sameRatesNB sameRatesT = 41 / 500 := by
    simp [crudeRate, Fin.sum_univ_two, sameRatesNB, sameRatesT]
    norm_num
  have hDA : directlyStandardizedRate sameRatesNA sameRatesT = 7 / 250 := by
    simp [directlyStandardizedRate, populationShare, Fin.sum_univ_two, sameRatesNA, sameRatesT]
    norm_num
  have hDB : directlyStandardizedRate sameRatesNB sameRatesT = 41 / 500 := by
    simp [directlyStandardizedRate, populationShare, Fin.sum_univ_two, sameRatesNB, sameRatesT]
    norm_num
  have hlink : directlyStandardizedRate sameRatesNB sameRatesT -
      directlyStandardizedRate sameRatesNA sameRatesT = 27 / 500 := by
    rw [hDA, hDB]
    norm_num
  have hdiff : crudeRate sameRatesNB sameRatesT - crudeRate sameRatesNA sameRatesT = 27 / 500 := by
    rw [hA, hB]
    norm_num
  have hprod := (crudeRate_sub_crudeRate_of_same_rates sameRatesNA sameRatesNB sameRatesT).2
  exact ⟨hlink, by rw [hdiff, hlink], hprod⟩

/-- Sizes `(60, 40)` for population 1 in the decomposition group. -/
def decN1 : Fin 2 → ℝ := ![60, 40]

/-- Rates `(2, 10)` for population 1. -/
def decT1 : Fin 2 → ℝ := ![2, 10]

/-- Sizes `(30, 70)` for population 2. -/
def decN2 : Fin 2 → ℝ := ![30, 70]

/-- Rates `(3, 8)` for population 2. -/
def decT2 : Fin 2 → ℝ := ![3, 8]

/-- Averaged-standard decomposition sums to `13/10`, matching the crude difference. -/
theorem decomposition_example :
    ((∑ i, (populationShare decN2 i + populationShare decN1 i) / 2 * decT2 i -
      ∑ i, (populationShare decN2 i + populationShare decN1 i) / 2 * decT1 i) +
    (∑ i, (decT2 i + decT1 i) / 2 * populationShare decN2 i -
      ∑ i, (decT2 i + decT1 i) / 2 * populationShare decN1 i)) = 13 / 10 ∧
    crudeRate decN2 decT2 - crudeRate decN1 decT1 = 13 / 10 ∧
    crudeRate decN2 decT2 - crudeRate decN1 decT1 =
      ((∑ i, (populationShare decN2 i + populationShare decN1 i) / 2 * decT2 i -
        ∑ i, (populationShare decN2 i + populationShare decN1 i) / 2 * decT1 i) +
      (∑ i, (decT2 i + decT1 i) / 2 * populationShare decN2 i -
        ∑ i, (decT2 i + decT1 i) / 2 * populationShare decN1 i)) ∧
    0 < crudeRate decN1 decT1 ∧
    0 < crudeRate decN2 decT2 := by
  have hC1 : crudeRate decN1 decT1 = 26 / 5 := by
    simp [crudeRate, Fin.sum_univ_two, decN1, decT1]
    norm_num
  have hC2 : crudeRate decN2 decT2 = 13 / 2 := by
    simp [crudeRate, Fin.sum_univ_two, decN2, decT2]
    norm_num
  have hB : ((∑ i, (populationShare decN2 i + populationShare decN1 i) / 2 * decT2 i -
      ∑ i, (populationShare decN2 i + populationShare decN1 i) / 2 * decT1 i) +
    (∑ i, (decT2 i + decT1 i) / 2 * populationShare decN2 i -
      ∑ i, (decT2 i + decT1 i) / 2 * populationShare decN1 i)) = 13 / 10 := by
    simp [populationShare, Fin.sum_univ_two, decN1, decN2, decT1, decT2]
    norm_num
  have hdiff : crudeRate decN2 decT2 - crudeRate decN1 decT1 = 13 / 10 := by
    rw [hC1, hC2]
    norm_num
  have hKit := crudeRate_sub_crudeRate decN1 decN2 decT1 decT2
  have hpos1 : 0 < crudeRate decN1 decT1 := by
    rw [hC1]
    norm_num
  have hpos2 : 0 < crudeRate decN2 decT2 := by
    rw [hC2]
    norm_num
  exact ⟨hB, hdiff, hKit, hpos1, hpos2⟩

/-- Single-standard sum is `11/5`, differing from `13/10` by `-9/10`. -/
theorem single_standard_interaction :
    (∑ i, populationShare decN1 i * (decT2 i - decT1 i) +
      ∑ i, decT1 i * (populationShare decN2 i - populationShare decN1 i)) = 11 / 5 ∧
    (∑ i, populationShare decN1 i * (decT2 i - decT1 i) +
      ∑ i, decT1 i * (populationShare decN2 i - populationShare decN1 i)) ≠ 13 / 10 ∧
    (crudeRate decN2 decT2 - crudeRate decN1 decT1) -
      ((∑ i, populationShare decN1 i * (decT2 i - decT1 i) +
        ∑ i, decT1 i * (populationShare decN2 i - populationShare decN1 i))) = -9 / 10 := by
  have hC1 : crudeRate decN1 decT1 = 26 / 5 := by
    simp [crudeRate, Fin.sum_univ_two, decN1, decT1]
    norm_num
  have hC2 : crudeRate decN2 decT2 = 13 / 2 := by
    simp [crudeRate, Fin.sum_univ_two, decN2, decT2]
    norm_num
  have hS : (∑ i, populationShare decN1 i * (decT2 i - decT1 i) +
      ∑ i, decT1 i * (populationShare decN2 i - populationShare decN1 i)) = 11 / 5 := by
    simp [populationShare, Fin.sum_univ_two, decN1, decN2, decT1, decT2]
    norm_num
  have hdiff : crudeRate decN2 decT2 - crudeRate decN1 decT1 = 13 / 10 := by
    rw [hC1, hC2]
    norm_num
  have hres : (crudeRate decN2 decT2 - crudeRate decN1 decT1) -
      ((∑ i, populationShare decN1 i * (decT2 i - decT1 i) +
        ∑ i, decT1 i * (populationShare decN2 i - populationShare decN1 i))) = -9 / 10 := by
    rw [hdiff, hS]
    norm_num
  exact ⟨hS, by rw [hS]; norm_num, hres⟩

/-- Deaths `(3, 12)` for the crude death rate group. -/
def crudeDeathD : Fin 2 → ℝ := ![3, 12]

/-- Exposures `(300, 400)`. -/
def crudeDeathE : Fin 2 → ℝ := ![300, 400]

/-- Exposures are positive. -/
theorem crudeDeathE_pos : ∀ i, 0 < crudeDeathE i := by
  intro i
  fin_cases i <;> norm_num [crudeDeathE]

/-- Crude rate of central death rates is `3/140`, via `crudeRate_centralDeathRate`. -/
theorem crude_death_rate_example :
    crudeRate crudeDeathE (fun i => centralDeathRate (crudeDeathD i) (crudeDeathE i)
      (crudeDeathE_pos i)) = 3 / 140 := by
  rw [crudeRate_centralDeathRate crudeDeathD crudeDeathE crudeDeathE_pos]
  norm_num [Fin.sum_univ_two, crudeDeathD, crudeDeathE]

/-- The `centerMass` bridge evaluates the crude rate of population 1 as `26/5`. -/
theorem centerMass_bridge_example : Finset.univ.centerMass decN1 decT1 = 26 / 5 := by
  rw [← crudeRate_eq_centerMass]
  simp [crudeRate, Fin.sum_univ_two, decN1, decT1]
  norm_num

/-- The standardization bridge: standardizing to `(50, 50)` is the crude rate of
  the standard, `11/200`. -/
theorem standardization_bridge_example :
    directlyStandardizedRate sameRatesS sameRatesT = crudeRate sameRatesS sameRatesT ∧
    crudeRate sameRatesS sameRatesT = 11 / 200 := by
  refine ⟨directlyStandardizedRate_eq_crudeRate sameRatesS sameRatesT, ?_⟩
  simp [crudeRate, Fin.sum_univ_two, sameRatesS, sameRatesT]
  norm_num

/-- Population 1 is valid. -/
theorem decN1_valid : IsValidPopulation decN1 where
  nonneg i := by fin_cases i <;> norm_num [decN1]
  sum_pos := by norm_num [Fin.sum_univ_two, decN1]

/-- The standard `(50, 50)` is valid. -/
theorem sameRatesS_valid : IsValidPopulation sameRatesS where
  nonneg i := by fin_cases i <;> norm_num [sameRatesS]
  sum_pos := by norm_num [Fin.sum_univ_two, sameRatesS]

/-- Valid-population bounds: shares in `[0, 1]` summing to `1`, and crude and
  standardized rates between the smallest and largest category rate. -/
theorem valid_population_bounds :
    populationShare decN1 0 ∈ Set.Icc (0 : ℝ) 1 ∧
    ∑ i, populationShare decN1 i = 1 ∧
    crudeRate decN1 decT1 ∈ Set.Icc (2 : ℝ) 10 ∧
    directlyStandardizedRate sameRatesS sameRatesT ∈ Set.Icc (1 / 100 : ℝ) (1 / 10) := by
  have hT1 : ∀ i, decT1 i ∈ Set.Icc (2 : ℝ) 10 := by
    intro i
    fin_cases i <;> norm_num [decT1]
  have hT : ∀ i, sameRatesT i ∈ Set.Icc (1 / 100 : ℝ) (1 / 10) := by
    intro i
    fin_cases i <;> norm_num [sameRatesT]
  exact ⟨populationShare_mem_Icc decN1_valid 0, sum_populationShare decN1_valid.sum_pos.ne',
    crudeRate_mem_Icc decN1_valid hT1, directlyStandardizedRate_mem_Icc sameRatesS_valid hT⟩

/-- Signed sizes `(-1, 2)` with total `1`. -/
def signedSizes : Fin 2 → ℝ := ![-1, 2]

/-- Rates `(0, 1)` for the signed population. -/
def signedRates : Fin 2 → ℝ := ![0, 1]

/-- Signed sizes are not a valid population, and outside the predicate the share
  `-1` and crude rate `2` lose their demographic meaning. -/
theorem signed_population_excluded :
    ¬ IsValidPopulation signedSizes ∧
    populationShare signedSizes 0 = -1 ∧
    crudeRate signedSizes signedRates = 2 := by
  refine ⟨fun h => ?_, ?_, ?_⟩
  · have h0 := h.nonneg 0
    norm_num [signedSizes] at h0
  · simp [populationShare, Fin.sum_univ_two, signedSizes]
    norm_num
  · simp [crudeRate, Fin.sum_univ_two, signedSizes, signedRates]
    norm_num

/-- All-zero sizes `(0, 0)` for boundary exclusion. -/
def zeroSizes : Fin 2 → ℝ := ![0, 0]

/-- Empty sizes on `Fin 0` for boundary exclusion. -/
def emptySizes : Fin 0 → ℝ := fun _ => 1

/-- All-zero total is `0`, so the population is not valid; crude rate junk `0`. -/
theorem zero_total_excluded :
    ∑ i, zeroSizes i = 0 ∧
    ¬ IsValidPopulation zeroSizes ∧
    crudeRate zeroSizes sameRatesT = 0 ∧
    directlyStandardizedRate zeroSizes sameRatesT = 0 ∧
    populationShare zeroSizes 0 = 0 := by
  have hsum : ∑ i, zeroSizes i = 0 := by norm_num [Fin.sum_univ_two, zeroSizes]
  refine ⟨hsum, ?_, ?_, ?_, ?_⟩
  · exact fun h => (lt_irrefl (0 : ℝ)) (hsum ▸ h.sum_pos)
  · simp [crudeRate, Fin.sum_univ_two, zeroSizes, sameRatesT]
  · simp [directlyStandardizedRate, populationShare, Fin.sum_univ_two, zeroSizes, sameRatesT]
  · simp [populationShare, Fin.sum_univ_two, zeroSizes]

/-- Empty total is `0`, so the population is not valid; crude rate junk `0`. -/
theorem empty_total_excluded :
    ∑ i, emptySizes i = 0 ∧
    ¬ IsValidPopulation emptySizes ∧
    crudeRate emptySizes (fun _ => 1) = 0 := by
  have hsum : ∑ i, emptySizes i = 0 := by simp
  refine ⟨hsum, ?_, ?_⟩
  · exact fun h => (lt_irrefl (0 : ℝ)) (hsum ▸ h.sum_pos)
  · simp [crudeRate]

/-- The share-weighted form of the crude rate holds without a nonzero total. -/
theorem share_weighted_at_zero_total :
    crudeRate zeroSizes sameRatesT = ∑ i, populationShare zeroSizes i * sameRatesT i :=
  crudeRate_eq_sum_populationShare_mul zeroSizes sameRatesT

end MathlibExtTest.Biology.Demography.LifeTable
