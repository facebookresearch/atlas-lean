/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.KaplanMeier
public import MathlibExt.Probability.Statistics.Survival.CoxPartialLikelihood
public import MathlibExt.Probability.Statistics.Survival.CompetingRisks

/-!
# Per-subject survival records and grouped censored data

`n` subjects are observed at `k` distinct, increasing times `t₀ < ⋯ < t_{k-1}`. Subject `i` is
recorded at the time with index `group i` and has an event flag `δ i` (`true` = event observed,
`false` = right-censored, the convention of `CoxPartialLikelihood`). Counting events and
censorings in each fiber of `group` gives grouped data `CensoredData.ofSubjects`, the input of the
Kaplan–Meier estimator.

This file is a finite counting bridge only: it proves that the grouped counts are the subject
counts, and that the Kaplan–Meier number at risk is the Cox risk-set size. The tie convention
(censoring after the deaths at a tied time) is the one of `KaplanMeier`. Delayed entry (left
truncation) is not encoded here.

## Main results

* `deaths_add_censored_ofSubjects`: deaths plus censorings at `tⱼ` is the fiber size.
* `size_ofSubjects`: the grouped sample has `n` subjects.
* `atRisk_ofSubjects`: the number at risk at `tⱼ` is `#{i | j ≤ group i}`.
* `numAtRisk_comp_group`: with `Tᵢ = t_{group i}`, the Cox risk-set size of subject `i` is the
  Kaplan–Meier number at risk at its time.
* `ofSubjects_comp_equiv`: the grouped data do not depend on the order of the subjects.
* `CompetingRiskData.toCensoredData_ofSubjects`: for subject records with a cause map, forgetting
  the causes of the grouped competing-risks data gives `CensoredData.ofSubjects`.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.KaplanMeier

open Finset

namespace CensoredData

variable {k n : ℕ}

/-- Grouped censored data from per-subject records: subject `i` is observed at `time (group i)`,
with an event if `δ i = true` and censored if `δ i = false`. The counts are
`deaths j = #{i | group i = j ∧ δ i = true}` and `censored j = #{i | group i = j ∧ δ i = false}`. -/
def ofSubjects (time : Fin k → ℝ) (htime : StrictMono time) (group : Fin n → Fin k)
    (δ : Fin n → Bool) : CensoredData k where
  time := time
  strictMono_time := htime
  deaths j := #{i | group i = j ∧ δ i = true}
  censored j := #{i | group i = j ∧ δ i = false}

variable (time : Fin k → ℝ) (htime : StrictMono time) (group : Fin n → Fin k) (δ : Fin n → Bool)

@[simp] theorem ofSubjects_time : (ofSubjects time htime group δ).time = time := rfl

@[simp] theorem ofSubjects_deaths (j : Fin k) :
    (ofSubjects time htime group δ).deaths j = #{i | group i = j ∧ δ i = true} := rfl

@[simp] theorem ofSubjects_censored (j : Fin k) :
    (ofSubjects time htime group δ).censored j = #{i | group i = j ∧ δ i = false} := rfl

/-- Deaths plus censorings at `time j` is the number of subjects recorded at `time j`. -/
theorem deaths_add_censored_ofSubjects (j : Fin k) :
    (ofSubjects time htime group δ).deaths j + (ofSubjects time htime group δ).censored j =
      #{i | group i = j} := by
  rw [ofSubjects_deaths, ofSubjects_censored, ← filter_filter, ← filter_filter]
  simpa using card_filter_add_card_filter_not (s := {i | group i = j}) (fun i => δ i = true)

/-- The grouped data contain all `n` subjects. -/
theorem size_ofSubjects : (ofSubjects time htime group δ).size = n := by
  simp only [size, deaths_add_censored_ofSubjects]
  rw [← card_eq_sum_card_fiberwise (fun i _ => mem_univ (group i)), card_univ, Fintype.card_fin]

/-- The number at risk at `time j` is the number of subjects recorded at `time j` or later. -/
theorem atRisk_ofSubjects (j : Fin k) :
    (ofSubjects time htime group δ).atRisk j = #{i | j ≤ group i} := by
  simp only [atRisk, deaths_add_censored_ofSubjects]
  rw [card_eq_sum_card_fiberwise (f := group) (t := {l | j ≤ l}) (fun i hi => by simpa using hi)]
  refine sum_congr rfl fun l hl => congrArg card ?_
  ext i
  simp only [mem_filter, mem_univ, true_and] at hl ⊢
  exact ⟨fun h => ⟨h ▸ hl, h⟩, fun h => h.2⟩

/-- There are no deaths and no censorings at a time where no subject is recorded. -/
theorem deaths_ofSubjects_eq_zero_and_censored_ofSubjects_eq_zero {j : Fin k}
    (hj : ∀ i, group i ≠ j) :
    (ofSubjects time htime group δ).deaths j = 0 ∧
      (ofSubjects time htime group δ).censored j = 0 := by
  simp [hj]

/-- Reordering the subjects does not change the grouped data. -/
theorem ofSubjects_comp_equiv (σ : Fin n ≃ Fin n) :
    ofSubjects time htime (group ∘ σ) (δ ∘ σ) = ofSubjects time htime group δ := by
  have key : ∀ p : Fin n → Prop, [DecidablePred p] → #{i | p (σ i)} = #{i | p i} := fun p _ =>
    card_equiv σ (by simp)
  simp only [ofSubjects, Function.comp_apply]
  congr 1 <;> funext j
  exacts [key fun i => group i = j ∧ δ i = true, key fun i => group i = j ∧ δ i = false]

end CensoredData

end MathlibExt.Probability.Statistics.KaplanMeier

namespace MathlibExt.Probability.Statistics.CompetingRisks

open Finset MathlibExt.Probability.Statistics.KaplanMeier

namespace CompetingRiskData

variable {k n r : ℕ}

/-- Grouped competing-risks data from per-subject records: subject `i` is observed at
`time (group i)`, failing from cause `c` if `cause i = some c` and censored if `cause i = none`. -/
def ofSubjects (time : Fin k → ℝ) (htime : StrictMono time) (group : Fin n → Fin k)
    (cause : Fin n → Option (Fin r)) : CompetingRiskData k r where
  time := time
  strictMono_time := htime
  events j c := #{i | group i = j ∧ cause i = some c}
  censored j := #{i | group i = j ∧ cause i = none}

/-- Forgetting the causes of subject-level competing-risks data gives the subject-level censored
data with event flag `δ i = (cause i).isSome`. -/
theorem toCensoredData_ofSubjects (time : Fin k → ℝ) (htime : StrictMono time)
    (group : Fin n → Fin k) (cause : Fin n → Option (Fin r)) :
    (ofSubjects time htime group cause).toCensoredData =
      CensoredData.ofSubjects time htime group fun i => (cause i).isSome := by
  simp only [toCensoredData, ofSubjects, CensoredData.ofSubjects, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none]
  congr 1
  funext j
  dsimp only [totalEvents]
  rw [card_eq_sum_card_fiberwise (f := cause) (t := univ.map Function.Embedding.some)
    (fun i hi => by obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 (mem_filter.1 hi).2.2; simp [hc]),
    sum_map]
  refine sum_congr rfl fun c _ => congrArg card ?_
  ext i
  simp only [mem_filter, mem_univ, true_and, Function.Embedding.some_apply]
  exact ⟨fun h => ⟨⟨h.1, by simp [h.2]⟩, h.2⟩, fun h => ⟨h.1.1, h.2⟩⟩

end CompetingRiskData

end MathlibExt.Probability.Statistics.CompetingRisks

namespace MathlibExt.Probability.Statistics.CoxPartialLikelihood

open Finset MathlibExt.Probability.Statistics.KaplanMeier

variable {k n : ℕ} {time : Fin k → ℝ}

/-- With observed times `Tᵢ = t_{group i}` at strictly increasing grouped times, the risk set of
subject `i` is the set of subjects recorded at the time of `i` or later (by
`StrictMono.le_iff_le`). -/
theorem riskSet_comp_group (htime : StrictMono time) (group : Fin n → Fin k) (i : Fin n) :
    riskSet (time ∘ group) i = ({l | group i ≤ group l} : Finset (Fin n)) := by
  ext l
  simp [riskSet, htime.le_iff_le]

/-- **Cox–Kaplan–Meier bridge**: with observed times `Tᵢ = t_{group i}`, the Cox risk-set size of
subject `i` is the Kaplan–Meier number at risk at the grouped time of `i`. -/
theorem numAtRisk_comp_group (htime : StrictMono time) (group : Fin n → Fin k)
    (δ : Fin n → Bool) (i : Fin n) :
    numAtRisk (time ∘ group) i = (CensoredData.ofSubjects time htime group δ).atRisk (group i) := by
  rw [numAtRisk, riskSet_comp_group htime, CensoredData.atRisk_ofSubjects]

end MathlibExt.Probability.Statistics.CoxPartialLikelihood
