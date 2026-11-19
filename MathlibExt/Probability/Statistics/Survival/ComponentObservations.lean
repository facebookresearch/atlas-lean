/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Probability.Statistics.Survival.Data

/-!
# Component failure observation tables

## i. Overview

An infrastructure component observation table records, for each
component, an inspection time (grouped at finitely many
increasing times) and an outcome: failure from one of finitely
many causes, or right-censoring at inspection. Components tied
at the same time and cause are counted together. This module
maps such tables into the canonical finite competing-risk
estimator (`CompetingRiskData.ofSubjects`, Aalen–Johansen
cumulative incidence) and recovers its finite identities for
table data: count formulas, all-censored consequences, mass
conservation, the single-cause Kaplan–Meier jumps, and the
cumulative-incidence bounds. The observation/estimator
separation is the point: no population consistency,
identifiability, or new estimator is claimed.

## ii. Key results

- `MathlibExt.Probability.Statistics.CompetingRisks.CompetingRiskData.componentFailureData`:
  single-cause component data from inspection groups and
  failed flags.
- `componentFailureData_events` / `componentFailureData_censored`:
  the tied-count formulas.
- `ofSubjects_cifIncrement_eq_zero_of_all_censored`,
  `ofSubjects_survivalBefore_eq_one_of_all_censored`, and
  `ofSubjects_kmTail_eq_one_of_all_censored`: all-censored
  tables estimate nothing and keep all mass.
- `ofSubjects_mass_identity`: all cause increments plus the
  leftover survival mass add to `1` for table data.
- `componentFailureData_cifIncrement_eq_kmMass` and
  `ofSubjects_cumulativeIncidence_bounds`: single-cause jumps
  and the `[0, 1]` monotone bounds.

## iii. Table of contents

- A. Component table adapter and counts
- B. All-censored tables
- C. Transported estimator identities
- D. Estimator identities for table data

## iv. References

- `MathlibExt.Probability.Statistics.Survival.CompetingRisks` for
  the competing-risk data and Aalen–Johansen estimator.
- `MathlibExt.Probability.Statistics.Survival.Data` for
  subject-level grouped data.
-/

@[expose] public section

open Finset MathlibExt.Probability.Statistics.KaplanMeier

namespace MathlibExt.Probability.Statistics.CompetingRisks

namespace CompetingRiskData

/-! ## A. Component table adapter and counts -/

/-- Single-cause infrastructure component failure data from an
observation table: component `i` is inspected at
`time (group i)` and has failed iff `failed i = true`;
otherwise it is right-censored at inspection. Components tied
at the same inspection time are counted together. No population
consistency or identifiability claim is made. -/
def componentFailureData {n k : ℕ} (time : Fin k → ℝ)
    (htime : StrictMono time) (group : Fin n → Fin k)
    (failed : Fin n → Bool) : CompetingRiskData k 1 :=
  ofSubjects time htime group (fun i => if failed i then some 0 else none)

/-- Failure counts of the component table: the failures recorded
at inspection time `j` are exactly the components inspected at
`j` with `failed = true`, ties counted with multiplicity. -/
theorem componentFailureData_events {n k : ℕ} (time : Fin k → ℝ)
    (htime : StrictMono time) (group : Fin n → Fin k)
    (failed : Fin n → Bool) (j : Fin k) :
    (componentFailureData time htime group failed).events j 0
      = (Finset.univ.filter (fun i => group i = j ∧ failed i = true)).card := by
  simp only [componentFailureData, CompetingRiskData.ofSubjects]
  congr 1
  apply Finset.filter_congr
  intro i _
  apply and_congr Iff.rfl
  cases failed i <;> simp

/-- Censoring counts of the component table. -/
theorem componentFailureData_censored {n k : ℕ} (time : Fin k → ℝ)
    (htime : StrictMono time) (group : Fin n → Fin k)
    (failed : Fin n → Bool) (j : Fin k) :
    (componentFailureData time htime group failed).censored j
      = (Finset.univ.filter (fun i => group i = j ∧ failed i = false)).card := by
  simp only [componentFailureData, CompetingRiskData.ofSubjects]
  congr 1
  apply Finset.filter_congr
  intro i _
  apply and_congr Iff.rfl
  cases failed i <;> simp

/-! ## B. All-censored tables -/

/-- An all-censored observation table records no events. -/
theorem ofSubjects_events_eq_zero_of_all_censored {n k r : ℕ}
    (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (cause : Fin n → Option (Fin r))
    (h : ∀ i, cause i = none) (j : Fin k) (c : Fin r) :
    (ofSubjects time htime group cause).events j c = 0 := by
  simp only [CompetingRiskData.ofSubjects]
  rw [Finset.card_filter_eq_zero_iff]
  intro i _
  simp [h i]

/-- An all-censored table has zero Aalen–Johansen increments. -/
theorem ofSubjects_cifIncrement_eq_zero_of_all_censored {n k r : ℕ}
    (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (cause : Fin n → Option (Fin r))
    (h : ∀ i, cause i = none) (j : Fin k) (c : Fin r) :
    (ofSubjects time htime group cause).cifIncrement j c = 0 := by
  have hev : (ofSubjects time htime group cause).events j c = 0 :=
    ofSubjects_events_eq_zero_of_all_censored time htime group cause h j c
  simp only [CompetingRiskData.cifIncrement, hev, Nat.cast_zero, zero_div, mul_zero]

/-- An all-censored table has zero estimated cumulative
incidence at every time. -/
theorem ofSubjects_cumulativeIncidence_eq_zero_of_all_censored
    {n k r : ℕ} (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (cause : Fin n → Option (Fin r))
    (h : ∀ i, cause i = none) (c : Fin r) (t : ℝ) :
    (ofSubjects time htime group cause).cumulativeIncidence c t = 0 := by
  simp only [CompetingRiskData.cumulativeIncidence]
  apply Finset.sum_eq_zero
  intro j _
  exact ofSubjects_cifIncrement_eq_zero_of_all_censored time htime group cause h j c

/-- An all-censored table has overall survival `1` before every
observation time. -/
theorem ofSubjects_survivalBefore_eq_one_of_all_censored {n k r : ℕ}
    (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (cause : Fin n → Option (Fin r))
    (h : ∀ i, cause i = none) (j : Fin k) :
    (ofSubjects time htime group cause).survivalBefore j = 1 := by
  have htot : ∀ l : Fin k, (ofSubjects time htime group cause).totalEvents l = 0 := by
    intro l
    simp only [CompetingRiskData.totalEvents]
    apply Finset.sum_eq_zero
    intro c _
    exact ofSubjects_events_eq_zero_of_all_censored time htime group cause h l c
  have hfac : ∀ l : Fin k,
      (ofSubjects time htime group cause).toCensoredData.kmFactor l = 1 := by
    intro l
    simp only [CompetingRiskData.toCensoredData, CensoredData.kmFactor, htot l,
      Nat.cast_zero, zero_div, sub_zero]
  simp only [CompetingRiskData.survivalBefore]
  apply Finset.prod_eq_one
  intro l _
  exact hfac l

/-- An all-censored table keeps all Kaplan–Meier mass in the
tail. -/
theorem ofSubjects_kmTail_eq_one_of_all_censored {n k r : ℕ}
    (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (cause : Fin n → Option (Fin r))
    (h : ∀ i, cause i = none) :
    (ofSubjects time htime group cause).toCensoredData.kmTail = 1 := by
  have htot : ∀ l : Fin k, (ofSubjects time htime group cause).totalEvents l = 0 := by
    intro l
    simp only [CompetingRiskData.totalEvents]
    apply Finset.sum_eq_zero
    intro c _
    exact ofSubjects_events_eq_zero_of_all_censored time htime group cause h l c
  have hfac : ∀ l : Fin k,
      (ofSubjects time htime group cause).toCensoredData.kmFactor l = 1 := by
    intro l
    simp only [CompetingRiskData.toCensoredData, CensoredData.kmFactor, htot l,
      Nat.cast_zero, zero_div, sub_zero]
  simp only [CensoredData.kmTail]
  apply Finset.prod_eq_one
  intro l _
  exact hfac l

/-! ## C. Transported estimator identities -/

/-- Finite mass conservation for an observation table,
transported from the canonical competing-risks identity: all
cause increments over follow-up plus the leftover survival mass
add to `1`. -/
private theorem ofSubjects_mass_identity_of
    (hmass : ∀ {k r : ℕ} (D : CompetingRiskData k r),
      (∑ c, ∑ j, D.cifIncrement j c) + D.toCensoredData.kmTail = 1)
    {n k r : ℕ} (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (cause : Fin n → Option (Fin r)) :
    (∑ c, ∑ j, (ofSubjects time htime group cause).cifIncrement j c)
      + (ofSubjects time htime group cause).toCensoredData.kmTail = 1 := by
  exact hmass _

/-- For the single-cause component table, the Aalen–Johansen
increments are the Kaplan–Meier jumps, transported from the
canonical single-cause identity. -/
private theorem componentFailureData_cifIncrement_eq_kmMass_of
    (hsingle : ∀ {k : ℕ} (D : CompetingRiskData k 1) (j : Fin k),
      D.cifIncrement j 0 = D.toCensoredData.kmMass j)
    {n k : ℕ} (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (failed : Fin n → Bool) (j : Fin k) :
    (componentFailureData time htime group failed).cifIncrement j 0
      = (componentFailureData time htime group failed).toCensoredData.kmMass j := by
  exact hsingle _ _

/-- Estimated cumulative incidence from an observation table
lies in `[0, 1]` and is non-decreasing in time, transported from
the canonical estimator bounds. -/
private theorem ofSubjects_cumulativeIncidence_bounds_of
    (hnn : ∀ {k r : ℕ} (D : CompetingRiskData k r) (c : Fin r) (t : ℝ),
      0 ≤ D.cumulativeIncidence c t)
    (hle : ∀ {k r : ℕ} (D : CompetingRiskData k r) (c : Fin r) (t : ℝ),
      D.cumulativeIncidence c t ≤ 1)
    (hmono : ∀ {k r : ℕ} (D : CompetingRiskData k r) (c : Fin r),
      Monotone (D.cumulativeIncidence c))
    {n k r : ℕ} (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (cause : Fin n → Option (Fin r))
    (c : Fin r) (t : ℝ) :
    0 ≤ (ofSubjects time htime group cause).cumulativeIncidence c t
      ∧ (ofSubjects time htime group cause).cumulativeIncidence c t ≤ 1
      ∧ Monotone ((ofSubjects time htime group cause).cumulativeIncidence c) := by
  exact ⟨hnn _ _ _, hle _ _ _, hmono _ _⟩

/-! ## D. Estimator identities for table data -/

/-- Finite mass conservation for an observation table: all
cause increments over follow-up plus the leftover survival
mass add to `1`. -/
theorem ofSubjects_mass_identity {n k r : ℕ}
    (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (cause : Fin n → Option (Fin r)) :
    (∑ c, ∑ j, (ofSubjects time htime group cause).cifIncrement j c)
      + (ofSubjects time htime group cause).toCensoredData.kmTail = 1 :=
  ofSubjects_mass_identity_of
    (fun D => D.sum_cumulativeIncidence_add_kmTail)
    time htime group cause

/-- For the single-cause component table, the Aalen–Johansen
increments are the Kaplan–Meier jumps. -/
theorem componentFailureData_cifIncrement_eq_kmMass {n k : ℕ}
    (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (failed : Fin n → Bool) (j : Fin k) :
    (componentFailureData time htime group failed).cifIncrement j 0
      = (componentFailureData time htime group
          failed).toCensoredData.kmMass j :=
  componentFailureData_cifIncrement_eq_kmMass_of
    (fun D j => D.cifIncrement_of_single_cause j)
    time htime group failed j

/-- Estimated cumulative incidence from an observation table
lies in `[0, 1]` and is non-decreasing in time. -/
theorem ofSubjects_cumulativeIncidence_bounds {n k r : ℕ}
    (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (cause : Fin n → Option (Fin r))
    (c : Fin r) (t : ℝ) :
    0 ≤ (ofSubjects time htime group cause).cumulativeIncidence c t
      ∧ (ofSubjects time htime group cause).cumulativeIncidence c t ≤ 1
      ∧ Monotone
        ((ofSubjects time htime group cause).cumulativeIncidence c) :=
  ofSubjects_cumulativeIncidence_bounds_of
    (fun D => D.cumulativeIncidence_nonneg)
    (fun D => D.cumulativeIncidence_le_one)
    (fun D => D.cumulativeIncidence_mono)
    time htime group cause c t

end CompetingRiskData

end MathlibExt.Probability.Statistics.CompetingRisks
