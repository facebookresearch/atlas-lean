/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.Probability.Statistics.Survival.ComponentObservations
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Component observation table checks

Concrete consumers of
`MathlibExt.Probability.Statistics.Survival.ComponentObservations`:
tied component counts, one competing failure among two causes,
an all-censored table, and the transported mass identity at a
concrete table.

## i. Overview

These are elaboration and count checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Tied counts and one competing failure
- B. All-censored and mass identity

## iv. References

- `MathlibExt.Probability.Statistics.Survival.ComponentObservations`
-/

open Finset
open MathlibExt.Probability.Statistics.CompetingRisks
open MathlibExt.Probability.Statistics.CompetingRisks.CompetingRiskData

namespace MathlibExtTest.Probability.Statistics.ComponentObservations

private theorem htime2 : StrictMono (![10, 20] : Fin 2 → ℝ) := by
  refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
  fin_cases i
  norm_num

/-! ## A. Tied counts and one competing failure -/

/-- Tied failures are counted together: two of three components
fail at the first recorded time, one is censored at the
second. -/
example : (componentFailureData ![10, 20] htime2 ![0, 0, 1]
    ![true, true, false]).events 0 0 = 2 := by
  rw [componentFailureData_events]
  decide

example : (componentFailureData ![10, 20] htime2 ![0, 0, 1]
    ![true, true, false]).censored 1 = 1 := by
  rw [componentFailureData_censored]
  decide

example : (componentFailureData ![10, 20] htime2 ![0, 0, 1]
    ![true, true, false]).events 1 0 = 0 := by
  rw [componentFailureData_events]
  decide

/-- One competing failure: with causes `(![some 0, none, some 1] : Fin 3 → Option (Fin 2))`
over groups `![0, 0, 1]`, cause `1` has no event at the first
time and one at the second; its first increment vanishes. -/
example : (ofSubjects ![10, 20] htime2 ![0, 0, 1]
    (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).events 0 1 = 0 := by
  decide

example : (ofSubjects ![10, 20] htime2 ![0, 0, 1]
    (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).events 1 1 = 1 := by
  decide

example : (ofSubjects ![10, 20] htime2 ![0, 0, 1]
    (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).cifIncrement 0 1 = 0 := by
  simp only [CompetingRiskData.cifIncrement,
    show (ofSubjects ![10, 20] htime2 ![0, 0, 1]
      (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).events 0 1 = 0 from by decide,
    Nat.cast_zero, zero_div, mul_zero]

/-! ## B. All-censored and mass identity -/

/-- An all-censored table: no increments, no cumulative
incidence, all mass in the tail. -/
example : (ofSubjects ![10, 20] htime2 ![0, 0, 1]
    (![none, none, none] : Fin 3 → Option (Fin 2))).cumulativeIncidence 0 30 = 0 :=
  ofSubjects_cumulativeIncidence_eq_zero_of_all_censored _ _ _ _
    (fun i => by fin_cases i <;> simp) 0 30

example : (ofSubjects ![10, 20] htime2 ![0, 0, 1]
    (![none, none, none] : Fin 3 → Option (Fin 2))).toCensoredData.kmTail = 1 :=
  ofSubjects_kmTail_eq_one_of_all_censored _ _ _ _
    (fun i => by fin_cases i <;> simp)

/-- Mass conservation and bounds at the tied table, as direct
clients of the canonical estimator identities. -/
example : (∑ c, ∑ j,
      (ofSubjects ![10, 20] htime2 ![0, 0, 1]
        (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).cifIncrement j c)
    + (ofSubjects ![10, 20] htime2 ![0, 0, 1]
        (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).toCensoredData.kmTail = 1 :=
  (ofSubjects ![10, 20] htime2 ![0, 0, 1]
    (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).sum_cumulativeIncidence_add_kmTail

example : (componentFailureData ![10, 20] htime2 ![0, 0, 1]
      ![true, true, false]).cifIncrement 0 0
    = (componentFailureData ![10, 20] htime2 ![0, 0, 1]
        ![true, true, false]).toCensoredData.kmMass 0 :=
  (componentFailureData ![10, 20] htime2 ![0, 0, 1]
    ![true, true, false]).cifIncrement_of_single_cause 0

example : 0 ≤ (ofSubjects ![10, 20] htime2 ![0, 0, 1]
      (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).cumulativeIncidence 1 30
    ∧ (ofSubjects ![10, 20] htime2 ![0, 0, 1]
        (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).cumulativeIncidence 1 30 ≤ 1 :=
  ⟨(ofSubjects ![10, 20] htime2 ![0, 0, 1]
      (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).cumulativeIncidence_nonneg 1 30,
    (ofSubjects ![10, 20] htime2 ![0, 0, 1]
      (![some 0, none, some 1] : Fin 3 → Option (Fin 2))).cumulativeIncidence_le_one 1 30⟩

#print axioms MathlibExt.Probability.Statistics.CompetingRisks.CompetingRiskData.componentFailureData_events
#print axioms MathlibExt.Probability.Statistics.CompetingRisks.CompetingRiskData.ofSubjects_cifIncrement_eq_zero_of_all_censored
#print axioms MathlibExt.Probability.Statistics.CompetingRisks.CompetingRiskData.ofSubjects_kmTail_eq_one_of_all_censored

end MathlibExtTest.Probability.Statistics.ComponentObservations
