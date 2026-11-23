/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Survival.AalenJohansenProductIntegral
public import MathlibExt.Probability.Statistics.Survival.LeftTruncation

/-!
# The Aalen–Johansen estimator under left truncation (delayed entry)

`n` subjects move through a finite state space `ι` and are observed on `k` distinct, increasing
grid times `t₀ < ⋯ < t_{k-1}`. Subject `i` enters the study at a real time `Lᵢ` (delayed entry),
is under observation until the grid time `Xᵢ = t_{exit i}` (censoring or end of follow-up), and
has a state path recorded on `Fin (k + 1)`: `state i m` is the state on `[t_{m-1}, t_m)` (with
`t_{-1} = -∞`), so `state i j.castSucc` is the state just before `tⱼ` and `state i j.succ` the
state at `tⱼ`, after any jump at `tⱼ`. Only the path on the observation window matters.

## Convention

The entry convention is that of `LeftTruncation`: the entry time is recorded by its grid index
`entry i : WithBot (Fin k)` (`LeftTruncation.entryIndex`), with `Lᵢ < tⱼ ↔ entry i < j`, and
subject `i` is **under observation** at `tⱼ` iff `entry i < j ≤ exit i`. The delayed-entry
multi-state counts are

* `Y_h(tⱼ) = #{i | entry i < j ≤ exit i, state just before tⱼ = h}` (`atRisk`),
* `N_{hl}(tⱼ) = #{i | entry i < j ≤ exit i, h just before tⱼ, l at tⱼ}` (`transitions`).

A subject entering exactly at `tⱼ` is not in the risk set at `tⱼ`. These counts define a
`MultiStateData` of `AalenJohansenProductIntegral` (`toMultiState`), and the left-truncated
**Aalen–Johansen estimator** `P̂(s, t) = ∏_{s < tⱼ ≤ t} (I + ΔΛ̂(tⱼ))` is the untruncated
estimator of that file evaluated on the delayed-entry risk sets (`transitionMatrix`).

A state can have nobody at risk at a grid time even without truncation (an absorbing state
always does). What delayed entry adds is an empty overall risk set in the middle of follow-up:
without truncation the total number under observation is non-increasing in `j`, but with delayed
entry it can drop to `0` at a grid time between two times where somebody is at risk. The
Nelson–Aalen jumps out of a state with an empty risk set are totalized to `0`, so the estimator
keeps the state's row equal to the identity row there
(`transitionMatrix_apply_of_atRisk_eq_zero`): the data identify no transition intensity out of
that state, and the identity row is a convention, not an estimate. In particular, if the overall
risk set is empty at a grid time in `(s, t]`, the product `P̂(s, t)` combines risk populations that
need not be connected (one subject observed only at `t₀` and another entering after `t₁` and
observed at `t₂`). Its entries are then totalized algebraic quantities, not estimates of
transition probabilities, just as `LeftTruncation`'s product-limit estimate is a survival estimate
only on `GapFree` data. The identities below are algebra and hold for all data.

## Main results

* `sum_transitions`: `∑_l N_{hl}(tⱼ) = Y_h(tⱼ)`, every subject at risk in `h` is somewhere at
  `tⱼ`; `sum_atRisk`: summed over the states, the risk sets are those of `LeftTruncation`.
* `hasProdIntegral_transitionMatrix`, `transitionMatrix_forward`, `transitionMatrix_mul`,
  `transitionMatrix_sum_row`, `transitionMatrix_nonneg`: the left-truncated Aalen–Johansen
  estimator is the product-integral of the delayed-entry Nelson–Aalen estimator, satisfies the
  forward equation and Chapman–Kolmogorov, and is a stochastic matrix (no hypothesis on the data).
* `transitionMatrix_apply_of_atRisk_eq_zero`: a state with nobody at risk in `(s, t]` keeps its
  identity row.
* `atRisk_le_atRisk_forgetEntry`, `transitionMatrix_eq_forgetEntry`,
  `transitionMatrix_eq_forgetEntry_of_entryTime`: **reduction to the untruncated estimator**:
  delayed entry only shrinks risk sets, and if every subject entered by `s` (`Lᵢ ≤ s`), the
  left-truncated estimator over `(s, t]` equals the untruncated one (all entries at `-∞`).
* Competing risks with delayed entry (`ofCompetingRisks`: one transient state `none`, absorption
  by cause `some c`, built from `LeftTruncation.DelayedEntryData` and a cause label):
  `transitionMatrix_none_none` gives `P̂₀₀(s, t) = ∏_{s < tⱼ ≤ t} (1 - dⱼ / Yⱼ)`, the delayed-entry
  product-limit factors of `LeftTruncation` (`transitionMatrix_none_none_eq_plSurvival` from
  before the first grid time, and `transitionMatrix_none_none_eq_kmSurvival`, Kaplan–Meier, under
  early entry); `transitionMatrix_none_some` gives the left-truncated cumulative incidence
  `F̂_c(s, t) = ∑_{s < tⱼ ≤ t} Ŝ(s, tⱼ-) d_{j,c} / Yⱼ`; `sum_condCumInc_add_condSurvival`: these
  totalized cumulative incidences and survival add up to `1`. `condSurvival` and `condCumInc` are
  estimates of survival and cumulative incidence over `(s, t]`, conditional on being event free at
  `s`, only when somebody is at risk at every grid time of `(s, t]`; otherwise they are totalized
  algebraic quantities without that interpretation.

## Scope

Finite counting on a fixed grid. Consistency, weak convergence, identification of the transition
intensities under independent truncation for general multi-state paths, and dependent truncation
are not treated (the univariate identification is in `LeftTruncation`). The product-integral of
general right-continuous intensities is not covered (as in `AalenJohansenProductIntegral`).

## References

* O. O. Aalen and S. Johansen, *An empirical transition matrix for non-homogeneous Markov chains
  based on censored observations*, Scand. J. Statist. 5 (1978), 141–150.
* P. K. Andersen, Ø. Borgan, R. D. Gill and N. Keiding, *Statistical Models Based on Counting
  Processes*, Springer (1993), Sections III.3 (left truncation) and IV.4.
* W.-Y. Tsai, N. P. Jewell and M.-C. Wang, *A note on the product-limit estimator under right
  censoring and left truncation*, Biometrika 74 (1987), 883–886.
-/

@[expose] public section

set_option autoImplicit false

namespace MathlibExt.Probability.Statistics.AalenJohansenLeftTruncation

open Finset Matrix
open MathlibExt.Probability.Statistics.AalenJohansenProductIntegral
open MathlibExt.Probability.Statistics.LeftTruncation

variable {k n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Two facts about time-ordered products -/

/-- Time-ordered products only see the factors at active indices. -/
theorem orderedProd_congr_left {A A' : Fin k → Matrix ι ι ℝ} {act : Fin k → Prop}
    [DecidablePred act] (h : ∀ j, act j → A j = A' j) : orderedProd A act = orderedProd A' act := by
  unfold orderedProd
  congr 1
  exact List.ofFn_inj.2 (funext fun j => if_ctx_congr Iff.rfl (fun hj => by rw [h j hj])
    fun _ => rfl)

/-- If row `h` of every active factor `Aⱼ` vanishes, row `h` of `∏ (I + Aⱼ)` is the identity row. -/
theorem orderedProd_apply_of_row_eq_zero : ∀ {k : ℕ} (A : Fin k → Matrix ι ι ℝ)
    (act : Fin k → Prop) [DecidablePred act] (h : ι), (∀ j, act j → ∀ l, A j h l = 0) →
    ∀ l, orderedProd A act h l = (1 : Matrix ι ι ℝ) h l
  | 0, A, act, _, h, _ => fun l => by rw [orderedProd_zero]
  | k + 1, A, act, _, h, hA => fun l => by
    have ih := orderedProd_apply_of_row_eq_zero (fun i : Fin k => A i.castSucc)
      (fun i => act i.castSucc) h fun j hj => hA _ hj
    rw [orderedProd_succ, mul_apply, sum_eq_single h
      (fun x _ hx => by rw [ih x, one_apply_ne (Ne.symm hx), zero_mul])
      (fun hh => absurd (mem_univ h) hh), ih h, one_apply_eq, one_mul]
    split_ifs with hl
    · rw [Matrix.add_apply, hA _ hl l, add_zero]
    · rfl

/-! ### Delayed-entry multi-state data -/

/-- Left-truncated multi-state data on `k` grid times: subject `i` enters at grid index
`entry i` (`⊥` = before `t₀`, see `LeftTruncation.entryIndex`), is observed until
`time (exit i)`, and `state i m` is its state on `[t_{m-1}, t_m)`. Only subjects entering strictly
before they leave are included. -/
structure DelayedEntryMultiStateData (k n : ℕ) (ι : Type*) where
  /-- The grid times, in increasing order. -/
  time : Fin k → ℝ
  /-- The grid times are strictly increasing. -/
  strictMono_time : StrictMono time
  /-- The grid index of the entry time (`⊥` if before the first grid time). -/
  entry : Fin n → WithBot (Fin k)
  /-- The grid index of the last observation time. -/
  exit : Fin n → Fin k
  /-- `state i j.castSucc` is the state just before `time j`, `state i j.succ` the state at
  `time j`. -/
  state : Fin n → Fin (k + 1) → ι
  /-- Inclusion: every subject enters strictly before it leaves. -/
  entry_lt_exit : ∀ i, entry i < exit i

namespace DelayedEntryMultiStateData

variable (D : DelayedEntryMultiStateData k n ι)

/-- The delayed-entry number at risk in state `h` at `tⱼ`:
`Y_h(tⱼ) = #{i | entry i < j ≤ exit i, state i just before tⱼ = h}`. -/
def atRisk (j : Fin k) (h : ι) : ℕ :=
  #{i | D.entry i < j ∧ j ≤ D.exit i ∧ D.state i j.castSucc = h}

/-- The delayed-entry number of subjects under observation at `tⱼ` that are in `h` just before
`tⱼ` and in `l` at `tⱼ` (for `l = h`: those that stay). -/
def transitions (j : Fin k) (h l : ι) : ℕ :=
  #{i | D.entry i < j ∧ j ≤ D.exit i ∧ D.state i j.castSucc = h ∧ D.state i j.succ = l}

/-- The delayed-entry counts as grouped multi-state data. -/
def toMultiState : MultiStateData k ι where
  time := D.time
  strictMono_time := D.strictMono_time
  transitions := D.transitions
  atRisk := D.atRisk

/-- The **left-truncated Aalen–Johansen estimator** `P̂(s, t) = ∏_{s < tⱼ ≤ t} (I + ΔΛ̂(tⱼ))`,
with Nelson–Aalen jumps computed on the delayed-entry risk sets. -/
noncomputable def transitionMatrix (s t : ℝ) : Matrix ι ι ℝ := D.toMultiState.transitionMatrix s t

/-! #### Counting -/

/-- Every subject at risk in `h` at `tⱼ` is in some state at `tⱼ`: `∑_l N_{hl}(tⱼ) = Y_h(tⱼ)`. -/
theorem sum_transitions (j : Fin k) (h : ι) : ∑ l, D.transitions j h l = D.atRisk j h := by
  rw [atRisk, card_eq_sum_card_fiberwise (f := fun i => D.state i j.succ) (t := univ)
    fun _ _ => mem_univ _]
  refine sum_congr rfl fun l _ => ?_
  rw [transitions, filter_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, and_assoc]

/-- The transitions out of `h` at `tⱼ` are at most the number at risk in `h`. -/
theorem sum_transitions_erase_le_atRisk (j : Fin k) (h : ι) :
    ∑ l ∈ univ.erase h, D.transitions j h l ≤ D.atRisk j h :=
  (sum_le_sum_of_subset (erase_subset h univ)).trans (D.sum_transitions j h).le

/-- Forgetting the states: the left-truncated survival data with the given event flags. -/
def toDelayedEntryData (event : Fin n → Bool) : DelayedEntryData k n where
  time := D.time
  strictMono_time := D.strictMono_time
  entry := D.entry
  exit := D.exit
  event := event
  entry_lt_exit := D.entry_lt_exit

/-- Summed over the states, the multi-state risk sets are the delayed-entry risk sets of
`LeftTruncation`, whatever the event flags. -/
theorem sum_atRisk (event : Fin n → Bool) (j : Fin k) :
    ∑ h, D.atRisk j h = (D.toDelayedEntryData event).atRisk j := by
  rw [DelayedEntryData.atRisk, card_eq_sum_card_fiberwise
    (f := fun i => D.state i j.castSucc) (t := univ) fun _ _ => mem_univ _]
  refine sum_congr rfl fun h _ => ?_
  rw [atRisk, filter_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, and_assoc, toDelayedEntryData]

/-! #### The estimator -/

/-- The left-truncated Aalen–Johansen estimator is the product-integral of the delayed-entry
Nelson–Aalen estimator. -/
theorem hasProdIntegral_transitionMatrix {s t : ℝ} (hst : s ≤ t) :
    HasProdIntegral D.toMultiState.naCumHazard s t (D.transitionMatrix s t) :=
  D.toMultiState.hasProdIntegral_transitionMatrix hst

/-- The forward equation for the left-truncated Aalen–Johansen estimator. -/
theorem transitionMatrix_forward (s t : ℝ) :
    D.transitionMatrix s t = 1 + ∑ j, if s < D.time j ∧ D.time j ≤ t then
      jumpProdLT D.time D.toMultiState.naIncrement s (D.time j) * D.toMultiState.naIncrement j
      else 0 :=
  D.toMultiState.transitionMatrix_forward s t

/-- Chapman–Kolmogorov for the left-truncated Aalen–Johansen estimator. -/
theorem transitionMatrix_mul {s u t : ℝ} (hsu : s ≤ u) (hut : u ≤ t) :
    D.transitionMatrix s u * D.transitionMatrix u t = D.transitionMatrix s t :=
  D.toMultiState.transitionMatrix_mul hsu hut

/-- The left-truncated Aalen–Johansen estimator has unit row sums. -/
theorem transitionMatrix_sum_row (s t : ℝ) (h : ι) : ∑ l, D.transitionMatrix s t h l = 1 :=
  D.toMultiState.transitionMatrix_sum_row s t h

/-- **The left-truncated Aalen–Johansen estimator is a stochastic matrix**: its entries are
non-negative (and its rows sum to `1`, `transitionMatrix_sum_row`), with no hypothesis on the
data. -/
theorem transitionMatrix_nonneg (s t : ℝ) (h l : ι) : 0 ≤ D.transitionMatrix s t h l :=
  D.toMultiState.transitionMatrix_nonneg D.sum_transitions_erase_le_atRisk s t h l

/-- With nobody at risk in `h` at `tⱼ`, the Nelson–Aalen jumps out of `h` are `0`. -/
theorem naIncrement_eq_zero_of_atRisk_eq_zero {j : Fin k} {h : ι} (h0 : D.atRisk j h = 0)
    (l : ι) : D.toMultiState.naIncrement j h l = 0 := by
  simp [MultiStateData.naIncrement, toMultiState, h0]

/-- **Empty risk sets freeze a state**: if nobody is at risk in `h` at any grid time in `(s, t]`,
row `h` of the estimator is the identity row. The data identify no intensity out of `h` there;
this row is the totalization convention. -/
theorem transitionMatrix_apply_of_atRisk_eq_zero {s t : ℝ} {h : ι}
    (h0 : ∀ j, s < D.time j → D.time j ≤ t → D.atRisk j h = 0) (l : ι) :
    D.transitionMatrix s t h l = (1 : Matrix ι ι ℝ) h l :=
  orderedProd_apply_of_row_eq_zero _ _ h
    (fun j hj l => D.naIncrement_eq_zero_of_atRisk_eq_zero (h0 j hj.1 hj.2) l) l

/-! #### Reduction to the untruncated estimator -/

/-- Forgetting the entry times: every subject is under observation from `-∞`. -/
def forgetEntry : DelayedEntryMultiStateData k n ι where
  time := D.time
  strictMono_time := D.strictMono_time
  entry _ := ⊥
  exit := D.exit
  state := D.state
  entry_lt_exit _ := WithBot.bot_lt_coe _

omit [Fintype ι] in
/-- Delayed entry only shrinks the risk sets. -/
theorem atRisk_le_atRisk_forgetEntry (j : Fin k) (h : ι) :
    D.atRisk j h ≤ D.forgetEntry.atRisk j h :=
  card_le_card (monotone_filter_right _ fun _ _ hi => ⟨WithBot.bot_lt_coe _, hi.2⟩)

omit [Fintype ι] in
/-- If every subject entered before `tⱼ`, the delayed-entry and untruncated risk sets at `tⱼ`
agree. -/
theorem atRisk_eq_atRisk_forgetEntry {j : Fin k} (hj : ∀ i, D.entry i < j) (h : ι) :
    D.atRisk j h = D.forgetEntry.atRisk j h := by
  unfold atRisk
  congr 1
  ext i
  simp [forgetEntry, hj i]

omit [Fintype ι] in
theorem transitions_eq_transitions_forgetEntry {j : Fin k} (hj : ∀ i, D.entry i < j) (h l : ι) :
    D.transitions j h l = D.forgetEntry.transitions j h l := by
  unfold transitions
  congr 1
  ext i
  simp [forgetEntry, hj i]

theorem naIncrement_eq_naIncrement_forgetEntry {j : Fin k} (hj : ∀ i, D.entry i < j) :
    D.toMultiState.naIncrement j = D.forgetEntry.toMultiState.naIncrement j := by
  ext h l
  simp only [MultiStateData.naIncrement, toMultiState, D.atRisk_eq_atRisk_forgetEntry hj,
    D.transitions_eq_transitions_forgetEntry hj]

/-- **Reduction to the untruncated Aalen–Johansen estimator**: if every subject entered before
every grid time in `(s, ∞)`, the left-truncated estimator over `(s, t]` is the untruncated one. -/
theorem transitionMatrix_eq_forgetEntry {s : ℝ} (hs : ∀ i j, s < D.time j → D.entry i < j)
    (t : ℝ) : D.transitionMatrix s t = D.forgetEntry.transitionMatrix s t :=
  orderedProd_congr_left fun j hj => D.naIncrement_eq_naIncrement_forgetEntry fun i => hs i j hj.1

/-- The reduction in terms of real entry times: if the entries are recorded by
`LeftTruncation.entryIndex` and every entry time is at most `s`, the left-truncated estimator
over `(s, t]` is the untruncated one. -/
theorem transitionMatrix_eq_forgetEntry_of_entryTime {s : ℝ} (L : Fin n → ℝ)
    (hentry : ∀ i, D.entry i = entryIndex D.time (L i)) (hL : ∀ i, L i ≤ s) (t : ℝ) :
    D.transitionMatrix s t = D.forgetEntry.transitionMatrix s t :=
  D.transitionMatrix_eq_forgetEntry (fun i j hj => by
    rw [hentry i, entryIndex_lt_iff D.strictMono_time]
    exact (hL i).trans_lt hj) t

end DelayedEntryMultiStateData

/-! ### Competing risks with delayed entry -/

section CompetingRisks

open MathlibExt.Probability.Statistics.CompetingRisks

variable {r : ℕ} (E : DelayedEntryData k n) (cause : Fin n → Fin r)

/-- The competing-risks path of subject `i`: transient (`none`) up to its exit, then absorbed by
`some (cause i)` at its exit if the event is observed, and still `none` if it is censored. -/
def crState (i : Fin n) (m : Fin (k + 1)) : Option (Fin r) :=
  if (E.exit i).succ ≤ m ∧ E.event i = true then some (cause i) else none

/-- Left-truncated competing-risks data, with the failure cause `cause i` of every subject whose
event is observed, as delayed-entry multi-state data on `Option (Fin r)`. -/
def ofCompetingRisks : DelayedEntryMultiStateData k n (Option (Fin r)) where
  time := E.time
  strictMono_time := E.strictMono_time
  entry := E.entry
  exit := E.exit
  state := crState E cause
  entry_lt_exit := E.entry_lt_exit

/-- The number of observed failures from cause `c` at `tⱼ`. -/
def causeDeaths (j : Fin k) (c : Fin r) : ℕ := #{i | E.exit i = j ∧ E.event i = true ∧ cause i = c}

/-- The failures from all causes are the observed events. -/
theorem sum_causeDeaths (j : Fin k) : ∑ c, causeDeaths E cause j c = E.deaths j := by
  rw [DelayedEntryData.deaths, card_eq_sum_card_fiberwise (f := cause) (t := univ)
    fun _ _ => mem_univ _]
  refine sum_congr rfl fun c _ => ?_
  rw [causeDeaths, filter_filter]
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and, and_assoc]

theorem crState_castSucc {i : Fin n} {j : Fin k} (hj : j ≤ E.exit i) :
    crState E cause i j.castSucc = none := by
  rw [crState, ite_eq_right]
  rintro ⟨h, -⟩
  exact (Fin.succ_le_castSucc_iff.1 h).not_ge hj

theorem crState_succ {i : Fin n} {j : Fin k} (hj : j ≤ E.exit i) :
    crState E cause i j.succ =
      if E.exit i = j ∧ E.event i = true then some (cause i) else none := by
  unfold crState
  refine if_congr ?_ rfl rfl
  rw [Fin.succ_le_succ_iff]
  exact and_congr_left' ⟨fun h => le_antisymm h hj, fun h => h.le⟩

/-- The delayed-entry number at risk in the transient state is that of `LeftTruncation`. -/
theorem atRisk_none (j : Fin k) : (ofCompetingRisks E cause).atRisk j none = E.atRisk j := by
  unfold DelayedEntryMultiStateData.atRisk DelayedEntryData.atRisk
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, crState_castSucc E cause h.2⟩⟩

/-- Nobody under observation is in an absorbing state just before a grid time. -/
theorem atRisk_some (j : Fin k) (c : Fin r) : (ofCompetingRisks E cause).atRisk j (some c) = 0 := by
  refine card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ hi => ?_)
  have h3 : crState E cause i j.castSucc = some c := hi.2.2
  rw [crState_castSucc E cause hi.2.1] at h3
  simp at h3

theorem transitions_some (j : Fin k) (c : Fin r) (l : Option (Fin r)) :
    (ofCompetingRisks E cause).transitions j (some c) l = 0 := by
  refine card_eq_zero.2 (filter_eq_empty_iff.2 fun i _ hi => ?_)
  have h3 : crState E cause i j.castSucc = some c := hi.2.2.1
  rw [crState_castSucc E cause hi.2.1] at h3
  simp at h3

/-- The transitions `none → some c` at `tⱼ` are the observed failures from cause `c`. -/
theorem transitions_none_some (j : Fin k) (c : Fin r) :
    (ofCompetingRisks E cause).transitions j none (some c) = causeDeaths E cause j c := by
  unfold DelayedEntryMultiStateData.transitions causeDeaths
  congr 1
  ext i
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨-, hj, -, hpost⟩
    have hpost' : crState E cause i j.succ = some c := hpost
    rw [crState_succ E cause hj] at hpost'
    split_ifs at hpost' with he
    · exact ⟨he.1, he.2, Option.some_injective _ hpost'⟩
  · rintro ⟨he, hev, hc⟩
    have hj : j ≤ E.exit i := he.ge
    refine ⟨he ▸ E.entry_lt_exit i, hj, crState_castSucc E cause hj, ?_⟩
    change crState E cause i j.succ = some c
    rw [crState_succ E cause hj, ite_eq_left ⟨he, hev⟩, hc]

theorem sum_erase_transitions_none (j : Fin k) :
    ∑ l ∈ univ.erase none, (ofCompetingRisks E cause).transitions j none l = E.deaths j := by
  have h := Fintype.sum_option fun l => (ofCompetingRisks E cause).transitions j none l
  rw [← add_sum_erase _ _ (mem_univ none)] at h
  rw [add_left_cancel h]
  simp only [transitions_none_some, sum_causeDeaths]

theorem naIncrement_none_none (j : Fin k) :
    (ofCompetingRisks E cause).toMultiState.naIncrement j none none = -E.hazardEst j := by
  rw [MultiStateData.naIncrement, ite_eq_left rfl]
  change -(∑ l' ∈ univ.erase none, ((ofCompetingRisks E cause).transitions j none l' : ℝ)) /
    ((ofCompetingRisks E cause).atRisk j none : ℝ) = _
  rw [← Nat.cast_sum, sum_erase_transitions_none, atRisk_none, neg_div]
  rfl

theorem naIncrement_none_some (j : Fin k) (c : Fin r) :
    (ofCompetingRisks E cause).toMultiState.naIncrement j none (some c) =
      (causeDeaths E cause j c : ℝ) / E.atRisk j := by
  rw [MultiStateData.naIncrement, ite_eq_right (Option.some_ne_none c).symm]
  change ((ofCompetingRisks E cause).transitions j none (some c) : ℝ) /
    ((ofCompetingRisks E cause).atRisk j none : ℝ) = _
  rw [transitions_none_some, atRisk_none]

theorem naIncrement_some (j : Fin k) (c : Fin r) (l : Option (Fin r)) :
    (ofCompetingRisks E cause).toMultiState.naIncrement j (some c) l = 0 :=
  (ofCompetingRisks E cause).naIncrement_eq_zero_of_atRisk_eq_zero (atRisk_some E cause j c) l

theorem noReturn_naIncrement (j : Fin k) :
    CompetingRiskData.NoReturn ((ofCompetingRisks E cause).toMultiState.naIncrement j) :=
  fun c => naIncrement_some E cause j c none

/-- The totalized delayed-entry product-limit product over `(s, t]`:
`Ŝ(s, t) = ∏_{s < tⱼ ≤ t} (1 - dⱼ / Yⱼ)`, where a grid time with nobody at risk contributes the
factor `1` (`LeftTruncation.DelayedEntryData.plFactor`).

It is defined for all data, but it estimates survival over `(s, t]`, conditional on being event
free at `s`, only when somebody is at risk at every grid time of `(s, t]`. Across a grid time with
an empty risk set the hazard is unidentified and the product combines risk populations that need
not be connected (one subject observed only at `t₀` and another entering after `t₁` and observed
at `t₂`), so it then has no conditional-survival interpretation; compare
`LeftTruncation.DelayedEntryData.plSurvival`, which is a survival estimate only under `GapFree`. -/
noncomputable def condSurvival (s t : ℝ) : ℝ := ∏ j with s < E.time j ∧ E.time j ≤ t, E.plFactor j

/-- The totalized left-truncated Aalen–Johansen sum for cause `c` over `(s, t]`:
`F̂_c(s, t) = ∑_{s < tⱼ ≤ t} Ŝ(s, tⱼ-) d_{j,c} / Yⱼ`, with the term `0` where `Yⱼ = 0`.

As for `condSurvival`, it estimates the cumulative incidence of cause `c` over `(s, t]`,
conditional on being event free at `s`, only when somebody is at risk at every grid time of
`(s, t]`; otherwise it is a totalized algebraic quantity without that interpretation. -/
noncomputable def condCumInc (c : Fin r) (s t : ℝ) : ℝ :=
  ∑ j with s < E.time j ∧ E.time j ≤ t,
    (∏ l with s < E.time l ∧ E.time l < E.time j, E.plFactor l) *
      ((causeDeaths E cause j c : ℝ) / E.atRisk j)

/-- **Left-truncated Aalen–Johansen survival entry = delayed-entry product-limit product**: the
transient-to-transient entry of the estimator over `(s, t]` is the totalized product
`condSurvival E s t = ∏_{s < tⱼ ≤ t} (1 - dⱼ / Yⱼ)`, for all data. -/
theorem transitionMatrix_none_none (s t : ℝ) :
    (ofCompetingRisks E cause).transitionMatrix s t none none = condSurvival E s t := by
  rw [DelayedEntryMultiStateData.transitionMatrix, MultiStateData.transitionMatrix, jumpProd,
    (CompetingRiskData.orderedProd_none_none _ _ (noReturn_naIncrement E cause)).2, condSurvival,
    prod_filter]
  refine prod_congr rfl fun j _ => ?_
  rw [naIncrement_none_none, ← sub_eq_add_neg]
  rfl

/-- **Left-truncated Aalen–Johansen cumulative-incidence entry**: the entry `none → some c` of
the estimator over `(s, t]` is the totalized sum
`condCumInc E cause c s t = ∑_{s < tⱼ ≤ t} Ŝ(s, tⱼ-) d_{j,c} / Yⱼ`, for all data. -/
theorem transitionMatrix_none_some (s t : ℝ) (c : Fin r) :
    (ofCompetingRisks E cause).transitionMatrix s t none (some c) = condCumInc E cause c s t := by
  rw [DelayedEntryMultiStateData.transitionMatrix, MultiStateData.transitionMatrix_forward,
    Matrix.add_apply, one_apply_ne (Option.some_ne_none c).symm, zero_add, Matrix.sum_apply,
    condCumInc, sum_filter]
  refine sum_congr rfl fun j _ => ?_
  rw [apply_ite (fun M : Matrix _ _ ℝ => M none (some c)), Matrix.zero_apply]
  refine if_congr Iff.rfl ?_ rfl
  rw [mul_apply, Fintype.sum_option,
    sum_eq_zero fun c' _ => by rw [naIncrement_some, mul_zero], add_zero, jumpProdLT,
    (CompetingRiskData.orderedProd_none_none _ _ (noReturn_naIncrement E cause)).2,
    naIncrement_none_some, prod_filter]
  congr 1
  refine prod_congr rfl fun l _ => ?_
  rw [naIncrement_none_none, ← sub_eq_add_neg]
  rfl

/-- **Row-sum identity**: the totalized cumulative incidences `condCumInc` over `(s, t]` and
`condSurvival` add up to `1`, for all data (the row sum of the stochastic matrix). They form one
conditional distribution given event-freeness at `s` only when somebody is at risk at every grid
time of `(s, t]`; otherwise the terms come from risk populations that need not be connected. -/
theorem sum_condCumInc_add_condSurvival (s t : ℝ) :
    ∑ c, condCumInc E cause c s t + condSurvival E s t = 1 := by
  have h := (ofCompetingRisks E cause).transitionMatrix_sum_row s t none
  rw [Fintype.sum_option] at h
  simp only [transitionMatrix_none_none, transitionMatrix_none_some] at h
  linarith

/-- The totalized cumulative incidences `condCumInc` are non-negative. -/
theorem condCumInc_nonneg (c : Fin r) (s t : ℝ) : 0 ≤ condCumInc E cause c s t :=
  transitionMatrix_none_some E cause s t c ▸
    (ofCompetingRisks E cause).transitionMatrix_nonneg s t none (some c)

/-- From before the first grid time, `condSurvival` is the totalized product `plSurvival` of
`LeftTruncation`, for all data; like `plSurvival`, it is a survival estimate only on `GapFree`
data. -/
theorem condSurvival_eq_plSurvival {s : ℝ} (hs : ∀ j, s < E.time j) (t : ℝ) :
    condSurvival E s t = E.plSurvival t := by
  rw [DelayedEntryData.plSurvival_eq_prod_all, condSurvival]
  exact prod_congr (filter_congr fun j _ => ⟨fun h => h.2, fun h => ⟨hs j, h⟩⟩) fun _ _ => rfl

/-- From before the first grid time, the transient-to-transient entry of the left-truncated
Aalen–Johansen estimator is the totalized product `plSurvival` of `LeftTruncation`, for all
data. -/
theorem transitionMatrix_none_none_eq_plSurvival {s : ℝ} (hs : ∀ j, s < E.time j) (t : ℝ) :
    (ofCompetingRisks E cause).transitionMatrix s t none none = E.plSurvival t := by
  rw [transitionMatrix_none_none, condSurvival_eq_plSurvival E hs]

/-- Under early entry (every entry precedes every observed exit time), the transient-to-transient
entry from before the first grid time is the Kaplan–Meier estimate of the untruncated data. -/
theorem transitionMatrix_none_none_eq_kmSurvival (hE : E.EntriesPrecedeExits) {s : ℝ}
    (hs : ∀ j, s < E.time j) (t : ℝ) :
    (ofCompetingRisks E cause).transitionMatrix s t none none = E.toCensoredData.kmSurvival t := by
  rw [transitionMatrix_none_none_eq_plSurvival E cause hs,
    DelayedEntryData.plSurvival_eq_kmSurvival hE]

end CompetingRisks

end MathlibExt.Probability.Statistics.AalenJohansenLeftTruncation
