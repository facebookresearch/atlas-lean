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
component, its exact recorded event or censoring time (grouped
at finitely many increasing times) and its outcome at that
time: failure from one of finitely many causes at the recorded
time, or right-censoring at the recorded time. This is the
usual right-censored subject-level encoding, not
current-status inspection data: a failure only known to have
occurred by an inspection time is interval-censored and is not
represented here. Components tied at the same recorded time
and cause are counted together. This module maps such tables
into the canonical finite competing-risk estimator
(`CompetingRiskData.ofSubjects`, Aalen–Johansen cumulative
incidence); the genuinely new adapter results are the count
formulas and the all-censored consequences, while the
canonical mass, single-cause, and bound identities apply to
the mapped data directly. No population consistency,
identifiability, or new estimator is claimed.

## ii. Key results

- `MathlibExt.Probability.Statistics.CompetingRisks.CompetingRiskData.componentFailureData`:
  single-cause component data from recorded-time groups and
  failed flags.
- `componentFailureData_events` / `componentFailureData_censored`:
  the tied-count formulas.
- `ofSubjects_cifIncrement_eq_zero_of_all_censored`,
  `ofSubjects_survivalBefore_eq_one_of_all_censored`, and
  `ofSubjects_kmTail_eq_one_of_all_censored`: all-censored
  tables estimate nothing and keep all mass.
- The canonical `sum_cumulativeIncidence_add_kmTail`,
  `cifIncrement_of_single_cause`, and cumulative-incidence
  bounds apply directly to the mapped table data.

## iii. Table of contents

- A. Component table adapter and counts
- B. All-censored tables

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
observation table: `time (group i)` is component `i`'s exact
recorded event or censoring time; `failed i = true` means the
failure occurred at that time, and `failed i = false` means
right-censoring at that time. Components tied at the same
recorded time are counted together. Current-status inspection
data (failure known only to have occurred by inspection) is
not represented. No population consistency or identifiability
claim is made. -/
def componentFailureData {n k : ℕ} (time : Fin k → ℝ)
    (htime : StrictMono time) (group : Fin n → Fin k)
    (failed : Fin n → Bool) : CompetingRiskData k 1 :=
  ofSubjects time htime group (fun i => if failed i then some 0 else none)

/-- Failure counts of the component table: the failures at
recorded time `j` are exactly the components grouped at `j`
with `failed = true`, ties counted with multiplicity. -/
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

end CompetingRiskData

end MathlibExt.Probability.Statistics.CompetingRisks
