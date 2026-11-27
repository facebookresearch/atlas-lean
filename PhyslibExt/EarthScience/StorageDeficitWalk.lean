/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Bioinformatics.Alignment.ScoreSignificance.SingleSequence

/-!
# Sequent-peak storage deficit from the Lindley walk

## i. Overview

For a finite horizon of time steps with required releases `R`
and inflows `Q` (one fixed volume unit), the signed deficits are
`dᵢ = Rᵢ - Qᵢ`. The storage deficit at time `t` — the
sequent-peak drawdown below a full reservoir, excess inflow
spilled — is the Lindley reflected walk
(`Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence.lindley`)
of the first `t` deficits. By the canonical Lindley/walk-maximum
duality it equals the largest net deficit over a final window
`[i, t)`, the maximum including the empty window (zero). The
storage capacity that meets the release over the whole horizon
is the worst such value over all times, the maximal segment
score of the deficit list. This module is the finite
time-index/list agreement between the hydrologic quantities and
the canonical list results; it proves no new recursion or
closed form, and includes no stationary queue, continuous
Skorokhod map, or periodic wrap.

## ii. Key results

- `EarthScience.requiredStorageAt`: the storage deficit at
  time `t` as a Lindley walk of the deficit list.
- `EarthScience.requiredStorageAt_succ`: the one-step reflected
  update.
- `EarthScience.suffixDeficitSum_le_requiredStorageAt` and
  `exists_suffixDeficitSum_eq_requiredStorageAt`: the deficit is
  exactly the maximum final-window net deficit.
- `EarthScience.requiredStorageAt_le_worst_and_exists_eq`:
  every time's deficit is at most the worst-required storage,
  and some time attains it.

## iii. Table of contents

- A. Deficit list and storage-deficit definitions
- B. Transported Lindley results
- C. Storage-deficit results from the canonical walk

## iv. References

- `CSLibExt.Bioinformatics.Alignment.ScoreSignificance.SingleSequence`
  for `lindley`, `walkMax`, `maxSegScore`, and their duality,
  prefix, and maximal-segment identification results.
- W. Rippl, "The capacity of storage reservoirs for water
  supply", *Minutes of the Proceedings of the Institution of
  Civil Engineers* 71 (1883), 270-278: the mass-curve
  (sequent-peak) construction of required storage from
  cumulative inflow and release over a finite horizon.
- V. T. Chow, D. R. Maidment, and L. W. Mays, *Applied
  Hydrology*, McGraw-Hill, 1988, Section 10.5 (reservoir
  capacity by the sequent-peak algorithm): the deficit
  recursion `K_{t+1} = max 0 (K_t + R_t - Q_t)` for an
  initially full reservoir that spills excess inflow, the
  finite nonperiodic horizon, and capacity as the maximum
  deficit over the horizon.
-/

@[expose] public section

open List
open Cslib.Bioinformatics.Alignment.ScoreSignificance.SingleSequence

namespace EarthScience

/-! ## A. Deficit list and storage-deficit definitions -/

/-- The finite list of signed hydrologic deficits `dᵢ = Rᵢ - Qᵢ`
(required release minus inflow, in one fixed volume unit) over
the time steps `0, …, n - 1`, in time order. -/
def deficitList {n : ℕ} (R Q : Fin n → ℝ) : List ℝ :=
  List.ofFn (fun i => R i - Q i)

/-- Storage deficit after the first `t` time steps: the Lindley
reflected walk of the first `t` deficits, i.e. the sequent-peak
drawdown below a full reservoir at time `t` (excess inflow
spilled). It equals the largest net deficit over a final window
`[i, t)`. For `t ≥ n` all `n` deficits enter, so the value is the
deficit at the end of the horizon. The storage capacity that meets
the release over the whole horizon is `worstRequiredStorage`, not
this value. -/
def requiredStorageAt {n : ℕ} (R Q : Fin n → ℝ) (t : ℕ) : ℝ :=
  lindley ((deficitList R Q).take t)

/-- Storage deficit at the end of the whole horizon. -/
def terminalStorageDeficit {n : ℕ} (R Q : Fin n → ℝ) : ℝ :=
  lindley (deficitList R Q)

/-- The signed deficit accumulated over the suffix of steps
`i, …, t - 1` (empty, hence zero, when `i ≥ t`, the step count
`t - i` being truncated subtraction); steps from `n` on contribute
nothing. -/
def suffixDeficitSum {n : ℕ} (R Q : Fin n → ℝ) (i t : ℕ) : ℝ :=
  (((deficitList R Q).drop i).take (t - i)).sum

/-- The worst required storage over all prefixes of the horizon:
the maximal segment score of the deficit list. -/
def worstRequiredStorage {n : ℕ} (R Q : Fin n → ℝ) : ℝ :=
  maxSegScore (deficitList R Q)

/-! ## B. Transported Lindley results -/

/-- A prefix of a list is the take of its length. -/
private lemma take_of_prefix {l s : List ℝ} (h : s <+: l) : l.take s.length = s := by
  obtain ⟨t, rfl⟩ := h
  rw [List.take_append, List.take_length, Nat.sub_self, List.take_zero, List.append_nil]

/-- Empty horizon: no storage is required before any step. -/
theorem requiredStorageAt_zero {n : ℕ} (R Q : Fin n → ℝ) :
    requiredStorageAt R Q 0 = 0 := by
  simp [requiredStorageAt, lindley]

/-- One-step update of required storage, transported from the
canonical Lindley concatenation rule: append step `t`'s deficit
and reflect at zero. -/
private lemma requiredStorageAt_succ_of
    (hconcat : ∀ (l : List ℝ) (a : ℝ),
      lindley (l ++ [a]) = max 0 (lindley l + a))
    {n : ℕ} (R Q : Fin n → ℝ) {t : ℕ} (ht : t < n) :
    requiredStorageAt R Q (t + 1)
      = max 0 (requiredStorageAt R Q t + (R ⟨t, ht⟩ - Q ⟨t, ht⟩)) := by
  have hlen : (deficitList R Q).length = n := List.length_ofFn
  have hmem : t < (deficitList R Q).length := by omega
  have htake : (deficitList R Q).take (t + 1)
      = (deficitList R Q).take t ++ [R ⟨t, ht⟩ - Q ⟨t, ht⟩] := by
    rw [List.take_add_one]
    have hget : (deficitList R Q)[t]? = some (R ⟨t, ht⟩ - Q ⟨t, ht⟩) := by
      rw [List.getElem?_eq_getElem hmem]
      exact congrArg some (List.getElem_ofFn hmem)
    rw [hget, Option.toList_some]
  unfold requiredStorageAt
  rw [htake, hconcat]

/-- The terminal storage deficit is the storage deficit at
`t = n` (not the horizon capacity, which is
`worstRequiredStorage`). -/
theorem terminalStorageDeficit_eq_at_length {n : ℕ} (R Q : Fin n → ℝ) :
    terminalStorageDeficit R Q = requiredStorageAt R Q n := by
  have hlen : (deficitList R Q).length = n := List.length_ofFn
  have htake : (deficitList R Q).take (deficitList R Q).length
      = deficitList R Q := List.take_length
  rw [hlen] at htake
  unfold terminalStorageDeficit requiredStorageAt
  rw [htake]

/-- Duality form, transported from the canonical Lindley/walkMax
duality: required storage at `t` is the walk maximum of the
time-reversed first `t` deficits. -/
private lemma requiredStorageAt_eq_walkMax_reverse_of
    (hdual : ∀ l : List ℝ, lindley l = walkMax l.reverse)
    {n : ℕ} (R Q : Fin n → ℝ) (t : ℕ) :
    requiredStorageAt R Q t
      = walkMax ((deficitList R Q).take t).reverse := by
  unfold requiredStorageAt
  exact hdual _

/-- Every suffix deficit is at most the required storage at `t`,
transported from the canonical prefix bound for `walkMax` and
the duality. -/
private lemma suffixDeficitSum_le_requiredStorageAt_of
    (hdual : ∀ l : List ℝ, lindley l = walkMax l.reverse)
    (hwm : ∀ {s l : List ℝ}, s <+: l → s.sum ≤ walkMax l)
    {n : ℕ} (R Q : Fin n → ℝ) {i t : ℕ} (hi : i ≤ t) (_ht : t ≤ n) :
    suffixDeficitSum R Q i t ≤ requiredStorageAt R Q t := by
  have hseg : (deficitList R Q).take t
      = (deficitList R Q).take i ++ (((deficitList R Q).drop i).take (t - i)) := by
    conv_lhs => rw [← Nat.add_sub_cancel' hi]
    rw [List.take_add]
  have hprefix : ((((deficitList R Q).drop i).take (t - i)).reverse)
      <+: (((deficitList R Q).take t).reverse) := by
    rw [hseg, List.reverse_append]
    exact List.prefix_append _ _
  unfold suffixDeficitSum requiredStorageAt
  rw [hdual, ← List.sum_reverse]
  exact hwm hprefix

/-- Some suffix attains the required storage at `t` (possibly
the empty suffix `i = t`, whose deficit is zero), transported
from the canonical prefix attainment for `walkMax` and the
duality. Hence the storage deficit at `t` is exactly the maximum
suffix deficit over `0 ≤ i ≤ t`, with the maximum including
zero. -/
private lemma exists_suffixDeficitSum_eq_requiredStorageAt_of
    (hdual : ∀ l : List ℝ, lindley l = walkMax l.reverse)
    (hwm : ∀ l : List ℝ, ∃ p, p <+: l ∧ p.sum = walkMax l)
    {n : ℕ} (R Q : Fin n → ℝ) {t : ℕ} (ht : t ≤ n) :
    ∃ i ≤ t, suffixDeficitSum R Q i t = requiredStorageAt R Q t := by
  obtain ⟨p, hp, hpeq⟩ := hwm (((deficitList R Q).take t).reverse)
  have hlenD : (deficitList R Q).length = n := List.length_ofFn
  have hlen : ((deficitList R Q).take t).length = t := by
    rw [List.length_take, hlenD, Nat.min_eq_left ht]
  have hplen : p.length ≤ t := by
    have h := hp.length_le
    rwa [List.length_reverse, hlen] at h
  have htsub : t - (t - p.length) = p.length := Nat.sub_sub_self hplen
  have hadd : t - p.length + p.length = t := Nat.sub_add_cancel hplen
  have hptake : ((((deficitList R Q).take t).reverse).take p.length) = p :=
    take_of_prefix hp
  have hpr : p.reverse = ((deficitList R Q).take t).drop (t - p.length) := by
    conv_lhs => rw [← hptake]
    rw [List.take_reverse, List.reverse_reverse, hlen]
  have hmain : (((deficitList R Q).drop (t - p.length)).take (t - (t - p.length)))
      = p.reverse := by
    rw [htsub, List.take_drop, hadd]
    exact hpr.symm
  refine ⟨t - p.length, Nat.sub_le t p.length, ?_⟩
  unfold suffixDeficitSum requiredStorageAt
  rw [hdual, ← hpeq, hmain, List.sum_reverse]

/-- The empty suffix has zero deficit. -/
theorem suffixDeficitSum_self {n : ℕ} (R Q : Fin n → ℝ) (t : ℕ) :
    suffixDeficitSum R Q t t = 0 := by
  unfold suffixDeficitSum
  rw [Nat.sub_self, List.take_zero, List.sum_nil]

/-- Required storage is nonnegative: the maximum defining it
includes the empty suffix. -/
private lemma requiredStorageAt_nonneg_of
    (hdual : ∀ l : List ℝ, lindley l = walkMax l.reverse)
    (hnn : ∀ l : List ℝ, 0 ≤ walkMax l)
    {n : ℕ} (R Q : Fin n → ℝ) (t : ℕ) :
    0 ≤ requiredStorageAt R Q t := by
  unfold requiredStorageAt
  rw [hdual]
  exact hnn _

/-- Required storage at every time is at most the worst over the
horizon, and some time attains the worst, transported from the
canonical maximal-segment/Lindley identification. -/
private lemma requiredStorageAt_le_worst_and_exists_eq_of
    (hmax : ∀ l : List ℝ,
      (∀ p, p <+: l → lindley p ≤ maxSegScore l)
        ∧ ∃ p, p <+: l ∧ lindley p = maxSegScore l)
    {n : ℕ} (R Q : Fin n → ℝ) :
    (∀ t, requiredStorageAt R Q t ≤ worstRequiredStorage R Q)
      ∧ ∃ t ≤ n, requiredStorageAt R Q t
          = worstRequiredStorage R Q := by
  obtain ⟨hle, p, hp, hpeq⟩ := hmax (deficitList R Q)
  have hlen : (deficitList R Q).length = n := List.length_ofFn
  have hplen : p.length ≤ n := by
    have h := hp.length_le
    rwa [hlen] at h
  have hptake : (deficitList R Q).take p.length = p := take_of_prefix hp
  refine ⟨?_, p.length, hplen, ?_⟩
  · intro t
    unfold requiredStorageAt worstRequiredStorage
    exact hle _ (List.take_prefix t (deficitList R Q))
  · unfold requiredStorageAt worstRequiredStorage
    rw [hptake, hpeq]

/-! ## C. Storage-deficit results from the canonical walk -/

/-- One-step update of required storage at a step `t < n`: append
step `t`'s deficit and reflect at zero. -/
theorem requiredStorageAt_succ {n : ℕ} (R Q : Fin n → ℝ)
    {t : ℕ} (ht : t < n) :
    requiredStorageAt R Q (t + 1)
      = max 0 (requiredStorageAt R Q t + (R ⟨t, ht⟩ - Q ⟨t, ht⟩)) :=
  requiredStorageAt_succ_of lindley_concat R Q ht

/-- Required storage at `t` is the walk maximum of the
time-reversed first `t` deficits. -/
theorem requiredStorageAt_eq_walkMax_reverse {n : ℕ}
    (R Q : Fin n → ℝ) (t : ℕ) :
    requiredStorageAt R Q t
      = walkMax ((deficitList R Q).take t).reverse :=
  requiredStorageAt_eq_walkMax_reverse_of lindley_eq_walkMax_reverse
    R Q t

/-- For `i ≤ t ≤ n`, every suffix deficit is at most the required
storage at `t`. -/
theorem suffixDeficitSum_le_requiredStorageAt {n : ℕ}
    (R Q : Fin n → ℝ) {i t : ℕ} (hi : i ≤ t) (ht : t ≤ n) :
    suffixDeficitSum R Q i t ≤ requiredStorageAt R Q t :=
  suffixDeficitSum_le_requiredStorageAt_of
    lindley_eq_walkMax_reverse sum_le_walkMax_of_prefix R Q hi ht

/-- For `t ≤ n`, some suffix attains the required storage at `t`
(possibly the empty suffix, whose deficit is zero). -/
theorem exists_suffixDeficitSum_eq_requiredStorageAt {n : ℕ}
    (R Q : Fin n → ℝ) {t : ℕ} (ht : t ≤ n) :
    ∃ i ≤ t, suffixDeficitSum R Q i t = requiredStorageAt R Q t :=
  exists_suffixDeficitSum_eq_requiredStorageAt_of
    lindley_eq_walkMax_reverse exists_prefix_sum_eq_walkMax R Q ht

/-- Required storage is nonnegative. -/
theorem requiredStorageAt_nonneg {n : ℕ} (R Q : Fin n → ℝ)
    (t : ℕ) :
    0 ≤ requiredStorageAt R Q t :=
  requiredStorageAt_nonneg_of lindley_eq_walkMax_reverse
    walkMax_nonneg R Q t

/-- Required storage at every time is at most the worst over
the horizon, and some time attains the worst. -/
theorem requiredStorageAt_le_worst_and_exists_eq {n : ℕ}
    (R Q : Fin n → ℝ) :
    (∀ t, requiredStorageAt R Q t ≤ worstRequiredStorage R Q)
      ∧ ∃ t ≤ n, requiredStorageAt R Q t
          = worstRequiredStorage R Q :=
  requiredStorageAt_le_worst_and_exists_eq_of
    maxSegScore_eq_max_lindley R Q

end EarthScience
