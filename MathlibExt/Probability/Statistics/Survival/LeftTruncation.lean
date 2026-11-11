/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.Data
public import MathlibExt.Probability.Statistics.Survival.NelsonAalen
public import MathlibExt.Probability.Statistics.Survival.Censoring
public import Mathlib.Probability.ConditionalProbability
import Mathlib.MeasureTheory.Measure.Real

/-!
# Delayed entry (left truncation) on a finite grid

`n` subjects are followed on `k` distinct, increasing grid times `t₀ < ⋯ < t_{k-1}`. Subject `i`
enters the study at a real time `Lᵢ` (delayed entry), leaves it at the grid time `Xᵢ = t_{exit i}`
with `Xᵢ = min(Tᵢ, Cᵢ)`, and has event flag `δᵢ = [Tᵢ ≤ Cᵢ]` (`true` = event observed, `false` =
right-censored, as in `CensoredData.ofSubjects`).

## Convention

* **Entry index.** Only the position of `Lᵢ` relative to the grid matters. It is recorded as
  `entry i : WithBot (Fin k)`, the index of the last grid time `≤ Lᵢ`, and `⊥` if `Lᵢ < t₀`
  (`entryIndex`). Then `Lᵢ < tⱼ ↔ entry i < j` (`entryIndex_lt_iff`).
* **Inclusion.** A left-truncated sample contains only subjects with `Lᵢ < Xᵢ`, i.e.
  `entry i < exit i` (`DelayedEntryData.entry_lt_exit`).
* **Risk set.** Subject `i` is at risk at `tⱼ` iff `Lᵢ < tⱼ ≤ Xᵢ`, i.e. `entry i < j ≤ exit i`.
  A subject entering exactly at `tⱼ` is *not* at risk at `tⱼ`. A subject leaving at `tⱼ`, by an
  event or by censoring, is at risk at `tⱼ` (censoring after the deaths at a tied time, the
  convention of `KaplanMeier`).

Empty cells are explicit: a grid time may have no exits, and, unlike the untruncated case, it may
have nobody at risk (`atRisk j = 0`) even between two times where somebody is at risk. The
product-limit and Nelson–Aalen estimators are therefore defined on the **support**
`{j | 0 < Yⱼ}` only. Across a zero-risk gap the data say nothing about the hazard, so these
estimators estimate conditional survival given survival to the start of the supported stretch,
not the unconditional survival function.

## Main results

* `deaths_add_censored`, `sum_deaths_add_censored`: grouped exits are the subject exits.
* `atRisk_add_card_exit_lt`: `Yⱼ + #{exitᵢ < j} = #{entryᵢ < j}` (entered minus exited).
* `deaths_add_censored_le_atRisk`, `deaths_eq_zero_of_atRisk_eq_zero`: exits at `tⱼ` are at risk
  at `tⱼ`; a zero-risk cell has no exits.
* `sum_plMass_add_plSurvival`: the product-limit jumps up to `t` and `Ŝ(t)` add up to `1`.
* `toCensoredData`, `atRisk_eq_atRisk_toCensoredData`: forgetting entries gives
  `CensoredData.ofSubjects`; when every entry precedes `tⱼ` the two numbers at risk agree.
* `plSurvival_eq_kmSurvival`, `nelsonAalen_eq_nelsonAalen`, `plMass_eq_kmMass`: **reduction to
  Kaplan–Meier**: if every entry precedes every observed exit time, the delayed-entry
  product-limit, Nelson–Aalen and jump quantities are exactly those of `toCensoredData`.
* `truncEventMass_div_truncAtRiskMass`, `truncEventMass_div_truncAtRiskMass_cond`:
  **identification of the hazard**: for `T`, `C`, `L` independent on the grid (`indepTruncLaw`;
  here `L` is a grid index and `L < j` means entry before `tⱼ`), if `P(L < j ≤ X) ≠ 0` then
  `P(X = j, δ = 1, L < j) / P(L < j ≤ X) = P(T = j) / P(T ≥ j)`, also under the law
  `μ[· | L < X]` of an included subject. Nothing is identified where `P(L < j ≤ X) = 0`, e.g. at
  the first grid point.

## Scope

Finite counting and finite-grid identification only. The Kaplan–Meier NPMLE property of
`KaplanMeier` is not claimed for the delayed-entry estimator (the left-truncated likelihood is a
product of conditional terms and is not treated), nor is dependent truncation, consistency, or
global survival beyond the supported times.

## References

* W.-Y. Tsai, N. P. Jewell and M.-C. Wang, *A note on the product-limit estimator under right
  censoring and left truncation*, Biometrika 74 (1987), 883–886.
* J. P. Klein and M. L. Moeschberger, *Survival Analysis*, 2nd ed., Springer (2003), Section 4.6.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.LeftTruncation

open Finset MathlibExt.Probability.Statistics.KaplanMeier

variable {k n : ℕ}

/-! ### Entry indices -/

/-- The grid index of a real entry time `L`: the last grid index `j` with `tⱼ ≤ L`, or `⊥` if
`L < t₀`. -/
noncomputable def entryIndex (time : Fin k → ℝ) (L : ℝ) : WithBot (Fin k) :=
  (univ.filter fun j => time j ≤ L).max

/-- **The entry convention**: `L < tⱼ` iff the entry index of `L` is below `j`. -/
theorem entryIndex_lt_iff {time : Fin k → ℝ} (htime : StrictMono time) (L : ℝ) (j : Fin k) :
    entryIndex time L < j ↔ L < time j := by
  classical
  rw [entryIndex, Finset.max_eq_sup_coe, Finset.sup_lt_iff (WithBot.bot_lt_coe j)]
  simp only [mem_filter, mem_univ, true_and, WithBot.coe_lt_coe]
  refine ⟨fun h => ?_, fun h a ha => htime.lt_iff_lt.1 (ha.trans_lt h)⟩
  by_contra hj
  exact lt_irrefl j (h j (not_lt.1 hj))

/-! ### Delayed-entry records -/

/-- Left-truncated survival data on `k` grid times: subject `i` enters at grid index `entry i`
(`⊥` = before `t₀`, see `entryIndex`), leaves at `time (exit i)`, with an event iff `event i`.
Only subjects entering strictly before they leave are included. -/
structure DelayedEntryData (k n : ℕ) where
  /-- The grid times, in increasing order. -/
  time : Fin k → ℝ
  /-- The grid times are strictly increasing. -/
  strictMono_time : StrictMono time
  /-- The grid index of the entry time (`⊥` if before the first grid time). -/
  entry : Fin n → WithBot (Fin k)
  /-- The grid index of the observed exit time `min(T, C)`. -/
  exit : Fin n → Fin k
  /-- `true` if the event is observed (`T ≤ C`), `false` if the subject is censored. -/
  event : Fin n → Bool
  /-- Inclusion: every subject enters strictly before it leaves (`L < X`). -/
  entry_lt_exit : ∀ i, entry i < exit i

namespace DelayedEntryData

variable (D : DelayedEntryData k n)

/-- The number of observed events at `tⱼ`. -/
def deaths (j : Fin k) : ℕ := #{i | D.exit i = j ∧ D.event i = true}

/-- The number of subjects censored at `tⱼ`. -/
def censored (j : Fin k) : ℕ := #{i | D.exit i = j ∧ D.event i = false}

/-- The delayed-entry number at risk at `tⱼ`: `Yⱼ = #{i | entryᵢ < j ≤ exitᵢ}`. -/
def atRisk (j : Fin k) : ℕ := #{i | D.entry i < j ∧ j ≤ D.exit i}

/-- Deaths plus censorings at `tⱼ` is the number of subjects leaving at `tⱼ`. -/
theorem deaths_add_censored (j : Fin k) :
    D.deaths j + D.censored j = #{i | D.exit i = j} := by
  rw [deaths, censored, ← filter_filter, ← filter_filter]
  simpa using card_filter_add_card_filter_not (s := {i | D.exit i = j}) (fun i => D.event i = true)

/-- Every subject leaves exactly once: the exits add up to `n`. -/
theorem sum_deaths_add_censored : ∑ j, (D.deaths j + D.censored j) = n := by
  simp only [deaths_add_censored]
  rw [← card_eq_sum_card_fiberwise (fun i _ => mem_univ (D.exit i)), card_univ, Fintype.card_fin]

/-- **Risk-set bookkeeping**: the number at risk at `tⱼ` plus the number who left before `tⱼ` is
the number who entered before `tⱼ`. -/
theorem atRisk_add_card_exit_lt (j : Fin k) :
    D.atRisk j + #{i | D.exit i < j} = #{i | D.entry i < j} := by
  rw [atRisk, ← card_union_of_disjoint]
  · congr 1
    ext i
    simp only [mem_union, mem_filter, mem_univ, true_and]
    refine ⟨fun h => h.elim And.left fun h => (D.entry_lt_exit i).trans (by exact_mod_cast h),
      fun h => ?_⟩
    rcases lt_or_ge (D.exit i) j with h' | h'
    · exact Or.inr h'
    · exact Or.inl ⟨h, h'⟩
  · refine disjoint_filter.2 fun i _ h h' => ?_
    exact absurd h.2 (not_le.2 h')

/-- Subjects leaving at `tⱼ` are at risk at `tⱼ`. -/
theorem deaths_add_censored_le_atRisk (j : Fin k) : D.deaths j + D.censored j ≤ D.atRisk j := by
  rw [deaths_add_censored]
  refine card_le_card fun i hi => ?_
  simp only [mem_filter, mem_univ, true_and] at hi ⊢
  exact ⟨hi ▸ D.entry_lt_exit i, hi.ge⟩

/-- The events at `tⱼ` are among those at risk. -/
theorem deaths_le_atRisk (j : Fin k) : D.deaths j ≤ D.atRisk j :=
  (Nat.le_add_right _ _).trans (D.deaths_add_censored_le_atRisk j)

/-- A grid time with nobody at risk has no events and no censorings. -/
theorem deaths_eq_zero_of_atRisk_eq_zero {j : Fin k} (h : D.atRisk j = 0) :
    D.deaths j = 0 ∧ D.censored j = 0 := by
  have := D.deaths_add_censored_le_atRisk j
  omega

/-! ### Product-limit and Nelson–Aalen estimators on the support -/

/-- The support of the delayed-entry data: grid indices with somebody at risk, `{j | 0 < Yⱼ}`. -/
def support : Finset (Fin k) := univ.filter fun j => 0 < D.atRisk j

theorem mem_support {j : Fin k} : j ∈ D.support ↔ 0 < D.atRisk j := by simp [support]

/-- The estimated discrete hazard `dⱼ / Yⱼ` (Lean-totalized: `0` where `Yⱼ = 0`). -/
noncomputable def hazardEst (j : Fin k) : ℝ := (D.deaths j : ℝ) / D.atRisk j

/-- The product-limit factor `1 - dⱼ / Yⱼ` (Lean-totalized: `1` where `Yⱼ = 0`). -/
noncomputable def plFactor (j : Fin k) : ℝ := 1 - D.hazardEst j

/-- The delayed-entry **product-limit estimate** `Ŝ(t) = ∏_{j ∈ support, tⱼ ≤ t} (1 - dⱼ / Yⱼ)`.

Grid times with nobody at risk are excluded: the data identify no hazard there. -/
noncomputable def plSurvival (t : ℝ) : ℝ :=
  ∏ j ∈ D.support with D.time j ≤ t, D.plFactor j

/-- The delayed-entry **Nelson–Aalen estimate** `Â(t) = ∑_{j ∈ support, tⱼ ≤ t} dⱼ / Yⱼ`. -/
noncomputable def nelsonAalen (t : ℝ) : ℝ :=
  ∑ j ∈ D.support with D.time j ≤ t, D.hazardEst j

/-- The product-limit jump at `tⱼ`: `Ŝ(tⱼ₋) · dⱼ / Yⱼ`, the product over supported `l < j`. -/
noncomputable def plMass (j : Fin k) : ℝ :=
  (∏ l ∈ D.support with l < j, D.plFactor l) * D.hazardEst j

/-- On the support, the product-limit factor is the genuine quotient `(Yⱼ - dⱼ) / Yⱼ`. -/
theorem plFactor_eq_div {j : Fin k} (h : 0 < D.atRisk j) :
    D.plFactor j = ((D.atRisk j : ℝ) - D.deaths j) / D.atRisk j := by
  have : (D.atRisk j : ℝ) ≠ 0 := by exact_mod_cast h.ne'
  rw [plFactor, hazardEst, sub_div, div_self this]

/-- Off the support the hazard estimate is `0` (because `dⱼ = 0`, not only by `x / 0 = 0`). -/
theorem hazardEst_eq_zero_of_not_mem {j : Fin k} (h : j ∉ D.support) : D.hazardEst j = 0 := by
  rw [mem_support, not_lt, Nat.le_zero] at h
  simp [hazardEst, (D.deaths_eq_zero_of_atRisk_eq_zero h).1]

theorem plFactor_eq_one_of_not_mem {j : Fin k} (h : j ∉ D.support) : D.plFactor j = 1 := by
  rw [plFactor, D.hazardEst_eq_zero_of_not_mem h, sub_zero]

theorem hazardEst_nonneg (j : Fin k) : 0 ≤ D.hazardEst j := by
  unfold hazardEst; positivity

theorem hazardEst_le_one (j : Fin k) : D.hazardEst j ≤ 1 :=
  div_le_one_of_le₀ (by exact_mod_cast D.deaths_le_atRisk j) (Nat.cast_nonneg _)

theorem plFactor_nonneg (j : Fin k) : 0 ≤ D.plFactor j := by
  rw [plFactor]; linarith [D.hazardEst_le_one j]

theorem plFactor_le_one (j : Fin k) : D.plFactor j ≤ 1 := by
  rw [plFactor]; linarith [D.hazardEst_nonneg j]

theorem plSurvival_nonneg (t : ℝ) : 0 ≤ D.plSurvival t :=
  prod_nonneg fun j _ => D.plFactor_nonneg j

theorem plSurvival_le_one (t : ℝ) : D.plSurvival t ≤ 1 :=
  prod_le_one₀ (fun j _ => D.plFactor_nonneg j) fun j _ => D.plFactor_le_one j

theorem plMass_nonneg (j : Fin k) : 0 ≤ D.plMass j :=
  mul_nonneg (prod_nonneg fun l _ => D.plFactor_nonneg l) (D.hazardEst_nonneg j)

/-- Restricting to the support changes nothing in the totalized product: off the support the
factor is `1` because nobody dies there. -/
theorem plSurvival_eq_prod_all (t : ℝ) :
    D.plSurvival t = ∏ j with D.time j ≤ t, D.plFactor j := by
  rw [plSurvival, support, filter_filter]
  refine prod_subset (fun j => by simp +contextual) fun j hj hj' => ?_
  refine D.plFactor_eq_one_of_not_mem fun hs => hj' ?_
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact ⟨(D.mem_support).1 hs, hj⟩

/-- **Telescoping**: the product-limit jumps at supported times `≤ t` and the estimate `Ŝ(t)`
add up to `1`. -/
theorem sum_plMass_add_plSurvival (t : ℝ) :
    ∑ j ∈ D.support with D.time j ≤ t, D.plMass j + D.plSurvival t = 1 := by
  set s := D.support.filter fun j => D.time j ≤ t
  have h := prod_one_sub_ordered s D.hazardEst
  have hprod : ∀ i ∈ s, ∏ l ∈ s with l < i, (1 - D.hazardEst l) =
      ∏ l ∈ D.support with l < i, D.plFactor l := fun i hi => by
    refine prod_congr ?_ fun _ _ => rfl
    ext l
    simp only [s, mem_filter] at hi ⊢
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h =>
      ⟨⟨h.1, (D.strictMono_time.monotone h.2.le).trans hi.2⟩, h.2⟩⟩
  rw [sum_congr rfl fun i hi => (by rw [plMass, mul_comm, ← hprod i hi] :
    D.plMass i = D.hazardEst i * ∏ l ∈ s with l < i, (1 - D.hazardEst l))]
  rw [plSurvival]
  change _ + ∏ j ∈ s, (1 - D.hazardEst j) = 1
  rw [h]
  ring

/-! ### Reduction to untruncated Kaplan–Meier -/

/-- Forgetting the entry times: the right-censored grouped data `CensoredData.ofSubjects` of the
exits and event flags. -/
noncomputable def toCensoredData : CensoredData k :=
  CensoredData.ofSubjects D.time D.strictMono_time D.exit D.event

@[simp] theorem deaths_toCensoredData (j : Fin k) : D.toCensoredData.deaths j = D.deaths j := rfl

@[simp] theorem censored_toCensoredData (j : Fin k) :
    D.toCensoredData.censored j = D.censored j := rfl

/-- The delayed-entry number at risk never exceeds the untruncated one. -/
theorem atRisk_le_atRisk_toCensoredData (j : Fin k) :
    D.atRisk j ≤ D.toCensoredData.atRisk j := by
  rw [toCensoredData, CensoredData.atRisk_ofSubjects]
  exact card_le_card (monotone_filter_right _ fun _ _ h => h.2)

/-- If every subject entered before `tⱼ`, the delayed-entry and untruncated numbers at risk at
`tⱼ` agree. -/
theorem atRisk_eq_atRisk_toCensoredData {j : Fin k} (h : ∀ i, D.entry i < j) :
    D.atRisk j = D.toCensoredData.atRisk j := by
  rw [toCensoredData, CensoredData.atRisk_ofSubjects, atRisk]
  congr 1
  ext i
  simp [h i]

/-- If every subject entered before `t₀`, the delayed-entry numbers at risk are the untruncated
ones at every grid time. -/
theorem atRisk_eq_of_entry_eq_bot (h : ∀ i, D.entry i = ⊥) (j : Fin k) :
    D.atRisk j = D.toCensoredData.atRisk j :=
  D.atRisk_eq_atRisk_toCensoredData fun i => by simp [h i]

section Reduction

variable {D}

/-- The hypothesis of the reduction: every entry precedes every observed exit time, i.e. the
first observed exit time. -/
def EntriesPrecedeExits (D : DelayedEntryData k n) : Prop := ∀ i i', D.entry i < D.exit i'

variable (hD : D.EntriesPrecedeExits)
include hD

/-- Under early entry, the number at risk at any time where somebody leaves is the untruncated
one. -/
theorem atRisk_eq_of_exit_eq {j : Fin k} {i' : Fin n} (hi' : D.exit i' = j) :
    D.atRisk j = D.toCensoredData.atRisk j :=
  D.atRisk_eq_atRisk_toCensoredData fun i => hi' ▸ hD i i'

theorem hazardEst_eq_of_entriesPrecedeExits (j : Fin k) :
    D.hazardEst j = (D.toCensoredData.deaths j : ℝ) / D.toCensoredData.atRisk j := by
  rw [hazardEst, deaths_toCensoredData]
  by_cases hd : D.deaths j = 0
  · simp [hd]
  · obtain ⟨i', hi'⟩ : ∃ i', D.exit i' = j ∧ D.event i' = true := by
      by_contra hne
      push Not at hne
      exact hd (card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ h => hne i h.1 h.2))
    rw [atRisk_eq_of_exit_eq hD hi'.1]

theorem plFactor_eq_kmFactor (j : Fin k) : D.plFactor j = D.toCensoredData.kmFactor j := by
  rw [plFactor, hazardEst_eq_of_entriesPrecedeExits hD, CensoredData.kmFactor]

/-- **Reduction of the product-limit estimate to Kaplan–Meier**: if every entry precedes every
observed exit time, the delayed-entry product-limit estimate is the Kaplan–Meier estimate of
`toCensoredData`. -/
theorem plSurvival_eq_kmSurvival (t : ℝ) :
    D.plSurvival t = D.toCensoredData.kmSurvival t := by
  rw [plSurvival_eq_prod_all, CensoredData.kmSurvival]
  exact prod_congr rfl fun j _ => plFactor_eq_kmFactor hD j

/-- **Reduction of the Nelson–Aalen estimate**: if every entry precedes every observed exit
time, the delayed-entry Nelson–Aalen estimate is the untruncated one. -/
theorem nelsonAalen_eq_nelsonAalen (t : ℝ) :
    D.nelsonAalen t = D.toCensoredData.nelsonAalen t := by
  rw [nelsonAalen, CensoredData.nelsonAalen, support, filter_filter]
  change _ = ∑ j with D.time j ≤ t, (D.toCensoredData.deaths j : ℝ) / D.toCensoredData.atRisk j
  refine (sum_subset (fun j => by simp +contextual) fun j hj hj' => ?_).trans
    (sum_congr rfl fun j _ => hazardEst_eq_of_entriesPrecedeExits hD j)
  refine D.hazardEst_eq_zero_of_not_mem fun hs => hj' ?_
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact ⟨(D.mem_support).1 hs, hj⟩

/-- **Reduction of the product-limit jumps**: if every entry precedes every observed exit time,
the delayed-entry jumps are the Kaplan–Meier jumps of `toCensoredData`. -/
theorem plMass_eq_kmMass (j : Fin k) : D.plMass j = D.toCensoredData.kmMass j := by
  rw [plMass, CensoredData.kmMass, hazardEst_eq_of_entriesPrecedeExits hD]
  congr 1
  rw [support, filter_filter]
  refine (prod_subset (fun l => by simp +contextual) fun l hl hl' => ?_).trans
    (prod_congr rfl fun l _ => plFactor_eq_kmFactor hD l)
  refine D.plFactor_eq_one_of_not_mem fun hs => hl' ?_
  simp only [mem_filter, mem_univ, true_and] at hl ⊢
  exact ⟨(D.mem_support).1 hs, hl⟩

end Reduction

end DelayedEntryData

/-! ### Identification of the hazard under independent truncation -/

section Identification

open MeasureTheory ProbabilityTheory MathlibExt.Probability.Statistics.Censoring

/-- The **observed truncated event mass** at grid point `j` under a joint law `μ` of
`((T, C), L)` on the grid: `P(min T C = j, T ≤ C, L < j)`, an observed event at `j` by a subject
that entered before `j`. -/
noncomputable def truncEventMass (μ : Measure ((Fin k × Fin k) × Fin k)) (j : Fin k) : ℝ :=
  μ.real {ω | min ω.1.1 ω.1.2 = j ∧ ω.1.1 ≤ ω.1.2 ∧ ω.2 < j}

/-- The **observed delayed-entry at-risk mass** at grid point `j` under a joint law `μ` of
`((T, C), L)`: `P(L < j ≤ min T C)`. -/
noncomputable def truncAtRiskMass (μ : Measure ((Fin k × Fin k) × Fin k)) (j : Fin k) : ℝ :=
  μ.real {ω | ω.2 < j ∧ j ≤ min ω.1.1 ω.1.2}

/-- The **inclusion event** of a left-truncated study: `L < min T C`. Only subjects in this event
are sampled. -/
def inclusion : Set ((Fin k × Fin k) × Fin k) := {ω | ω.2 < min ω.1.1 ω.1.2}

/-- The canonical **independent truncation model**: event time `T ~ pT`, censoring time
`C ~ pC` and entry time `L ~ pL` mutually independent. -/
noncomputable def indepTruncLaw (pT pC pL : PMF (Fin k)) : Measure ((Fin k × Fin k) × Fin k) :=
  (indepLaw pT pC).prod pL.toMeasure

instance (pT pC pL : PMF (Fin k)) : IsProbabilityMeasure (indepTruncLaw pT pC pL) := by
  unfold indepTruncLaw; infer_instance

/-- The probability `P(L < j)` that a subject has entered before grid point `j`. -/
noncomputable def entryMass (pL : PMF (Fin k)) (j : Fin k) : ℝ := pL.toMeasure.real {l | l < j}

/-- **Factorization of the truncated event mass** under independent truncation:
`P(min T C = j, T ≤ C, L < j) = P(T = j) P(C ≥ j) P(L < j)`. -/
theorem truncEventMass_indepTruncLaw (pT pC pL : PMF (Fin k)) (j : Fin k) :
    truncEventMass (indepTruncLaw pT pC pL) j =
      (pT j).toReal * survivalMass pC j * entryMass pL j := by
  have hE : {ω : (Fin k × Fin k) × Fin k | min ω.1.1 ω.1.2 = j ∧ ω.1.1 ≤ ω.1.2 ∧ ω.2 < j} =
      {ω : Fin k × Fin k | min ω.1 ω.2 = j ∧ ω.1 ≤ ω.2} ×ˢ {l | l < j} := by
    ext ⟨⟨t, c⟩, l⟩
    simp [and_assoc]
  rw [truncEventMass, hE, indepTruncLaw, measureReal_prod_prod, ← obsEventMass,
    obsEventMass_indepLaw, entryMass]

/-- **Factorization of the delayed-entry at-risk mass** under independent truncation:
`P(L < j ≤ min T C) = P(T ≥ j) P(C ≥ j) P(L < j)`. -/
theorem truncAtRiskMass_indepTruncLaw (pT pC pL : PMF (Fin k)) (j : Fin k) :
    truncAtRiskMass (indepTruncLaw pT pC pL) j =
      survivalMass pT j * survivalMass pC j * entryMass pL j := by
  have hR : {ω : (Fin k × Fin k) × Fin k | ω.2 < j ∧ j ≤ min ω.1.1 ω.1.2} =
      {ω : Fin k × Fin k | j ≤ min ω.1 ω.2} ×ˢ {l | l < j} := by
    ext ⟨⟨t, c⟩, l⟩
    simp [and_comm]
  rw [truncAtRiskMass, hR, indepTruncLaw, measureReal_prod_prod, ← obsAtRiskMass,
    obsAtRiskMass_indepLaw, entryMass]

/-- Under independent truncation the at-risk mass is nonzero iff `P(T ≥ j)`, `P(C ≥ j)` and
`P(L < j)` all are. In particular it is `0` at the first grid point, where `P(L < 0) = 0`. -/
theorem truncAtRiskMass_indepTruncLaw_ne_zero_iff (pT pC pL : PMF (Fin k)) (j : Fin k) :
    truncAtRiskMass (indepTruncLaw pT pC pL) j ≠ 0 ↔
      survivalMass pT j ≠ 0 ∧ survivalMass pC j ≠ 0 ∧ entryMass pL j ≠ 0 := by
  rw [truncAtRiskMass_indepTruncLaw, mul_ne_zero_iff, mul_ne_zero_iff, and_assoc]

/-- **Identification of the discrete hazard under independent left truncation and right
censoring**: if the delayed-entry at-risk mass `P(L < j ≤ X)` is nonzero, the observed ratio
`P(X = j, δ = 1, L < j) / P(L < j ≤ X)` is the hazard `P(T = j) / P(T ≥ j)` of `T` at `j`. -/
theorem truncEventMass_div_truncAtRiskMass (pT pC pL : PMF (Fin k)) (j : Fin k)
    (h : truncAtRiskMass (indepTruncLaw pT pC pL) j ≠ 0) :
    truncEventMass (indepTruncLaw pT pC pL) j / truncAtRiskMass (indepTruncLaw pT pC pL) j =
      hazard pT j := by
  obtain ⟨-, hC, hL⟩ := (truncAtRiskMass_indepTruncLaw_ne_zero_iff pT pC pL j).1 h
  rw [truncEventMass_indepTruncLaw, truncAtRiskMass_indepTruncLaw,
    mul_div_mul_right _ _ hL, mul_div_mul_right _ _ hC, hazard]

/-- Under the law of an included subject, `μ[· | L < X]`, the real mass of an event inside the
inclusion event is its unconditional mass divided by `P(L < X)`. -/
theorem measureReal_cond_inclusion (μ : Measure ((Fin k × Fin k) × Fin k)) {E : Set _}
    (hE : E ⊆ inclusion) : (μ[|inclusion]).real E = (μ.real inclusion)⁻¹ * μ.real E := by
  rw [measureReal_def, cond_apply (Set.toFinite _).measurableSet, Set.inter_eq_right.2 hE,
    ENNReal.toReal_mul, ENNReal.toReal_inv, measureReal_def, measureReal_def]

/-- **Identification from the sampled population**: in a left-truncated study only subjects with
`L < X` are observed, with law `μ[· | L < X]`. Under independent truncation, if the
unconditional at-risk mass `P(L < j ≤ X)` is nonzero, the observed event-to-at-risk ratio among
included subjects is the hazard of `T` at `j`. -/
theorem truncEventMass_div_truncAtRiskMass_cond (pT pC pL : PMF (Fin k)) (j : Fin k)
    (h : truncAtRiskMass (indepTruncLaw pT pC pL) j ≠ 0) :
    truncEventMass ((indepTruncLaw pT pC pL)[|inclusion]) j /
        truncAtRiskMass ((indepTruncLaw pT pC pL)[|inclusion]) j = hazard pT j := by
  set μ := indepTruncLaw pT pC pL
  have hEsub : {ω : (Fin k × Fin k) × Fin k | min ω.1.1 ω.1.2 = j ∧ ω.1.1 ≤ ω.1.2 ∧ ω.2 < j} ⊆
      inclusion := fun ω hω => by
    simp only [Set.mem_ofPred_eq, inclusion] at hω ⊢
    exact hω.1 ▸ hω.2.2
  have hRsub : {ω : (Fin k × Fin k) × Fin k | ω.2 < j ∧ j ≤ min ω.1.1 ω.1.2} ⊆ inclusion :=
    fun ω hω => hω.1.trans_le hω.2
  have hinc : μ.real inclusion ≠ 0 := fun h0 =>
    h (le_antisymm (h0 ▸ measureReal_mono hRsub) measureReal_nonneg)
  rw [truncEventMass, truncAtRiskMass, measureReal_cond_inclusion μ hEsub,
    measureReal_cond_inclusion μ hRsub, mul_div_mul_left _ _ (inv_ne_zero hinc)]
  exact truncEventMass_div_truncAtRiskMass pT pC pL j h

end Identification

end MathlibExt.Probability.Statistics.LeftTruncation
