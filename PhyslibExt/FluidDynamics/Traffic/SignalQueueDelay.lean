/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.Traffic.SignalQueueArea
public import CSLibExt.Algorithms.Networking.NetworkCalculus

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Cycle-average delay of the fixed-time signal queue

## i. Overview

The deterministic fluid queue at a fixed-time traffic signal over one cycle: constant arrival
rate `lam`, saturation service rate `mu`, red time `R`, green time `G`, empty at the start of
red. The queue area over the cycle is `lam * R ^ 2 * mu / (2 * (mu - lam))`
(`queueLen_integral_cycle`). This module normalizes that area by the positive arrival volume
`lam * (R + G)` and identifies the quotient with the arrival-average first-in-first-out delay.

Model and domain:

- One cycle `[0, R + G]` of the one-cycle, non-periodic queue `queueLen`: growth at rate `lam`
  during red, drainage at rate `mu - lam` during green until it clears, then empty. No
  spillback, lost time, platoon dispersion or random arrivals.
- Admitted domain: `0 < lam < mu`, `0 ≤ R`, `0 ≤ G` and strict capacity
  `lam * (R + G) < mu * G`. Strict capacity forces `0 < G`, so the cycle has positive length,
  and the queue clears at `R + lam * R / (mu - lam)`, strictly before the cycle ends. Capacity
  equality is excluded.
- Units: `lam` and `mu` in vehicles per unit time; `R`, `G`, times and delays in that time
  unit; queue lengths and counts in vehicles; the queue area in vehicle-time units.

Frozen conventions for the delay; they add no second queue model:

- Waiting map: `Cslib.Algorithms.Networking.NetworkCalculus.delay`, the virtual delay
  `inf {τ ≥ 0 | A s ≤ D (s + τ)}` of the vehicle arriving at time `s` when all earlier vehicles
  are served first, in `ℝ≥0∞`, with `⊤` if it is never served (J.-Y. Le Boudec and P. Thiran,
  *Network Calculus*, LNCS 2050, Section 1.1).
- Cumulative counts, with time `s : ℝ≥0` and counts in `ℝ≥0`: arrivals `A s = lam * s` and
  departures `D s = lam * s - queueLen lam mu R s`, both through `Real.toNNReal`. On the
  admitted domain `0 ≤ queueLen lam mu R s ≤ lam * s`, so both truncations are exact, `(A, D)`
  is a lossless flow pair and its backlog `A s - D s` is the queue length
  (`isFlowPair_and_backlog_eq_queueLen`, the physical-to-canonical bridge).
- Arrival measure: `ENNReal.ofReal lam • volume` on the half-open window `Set.Ico 0 (R + G)`,
  the Stieltjes measure of `s ↦ lam * s` there. The arrival volume is `lam * (R + G)`.
- Endpoints: a single instant has arrival measure zero, so the endpoints of the window do not
  matter. At `s = 0` the virtual delay is `0`, because the count `A 0 = 0` is already reached;
  for `0 < s ≤ mu * R / (mu - lam)` it is `R + lam * s / mu - s`, and `0` afterwards. Every
  arrival in the window is served before the cycle ends (by the clearance time, or on arrival
  after it), so the values of the one-cycle model after the cycle do not affect these delays.
- Totalized operations: real division only by the positive `2 * (mu - lam)` of the area
  formula, by the arrival volume and by `2 * (mu - lam) * (R + G)` in the normalized and
  averaged formulas; `ℝ≥0∞` division only by the positive finite
  `ENNReal.ofReal (lam * (R + G))`; the truncated subtraction in `backlog` and the
  `Real.toNNReal` counts are exact on the admitted domain.

Scope: positivity of the arrival volume, the normalized queue area, the flow-pair bridge, the
cycle occupancy identity (arrival-weighted delay equals queue area) and the arrival-average
delay. This is the fixed-signal instance only, not a general occupancy theorem. Excluded: any
stationary or long-run Little law, an occupancy theorem for other queues, a mean delay at zero
arrival volume, periodic or multi-cycle operation, finite-link spillback, and random arrivals.

## ii. Key results

- `FluidDynamics.Traffic.SignalQueue.arrivalVolume_pos`: the arrival volume of a clearing
  cycle is positive.
- `FluidDynamics.Traffic.SignalQueue.queueArea_div_arrivalVolume`: the queue area normalized
  by the arrival volume is `R ^ 2 * mu / (2 * (mu - lam) * (R + G))`.
- `FluidDynamics.Traffic.SignalQueue.isFlowPair_and_backlog_eq_queueLen`: arrivals and
  departures form a lossless flow pair whose backlog is the queue length.
- `FluidDynamics.Traffic.SignalQueue.arrivalWeighted_delay_eq_queueArea`: the
  arrival-weighted virtual delay over the cycle equals the queue area.
- `FluidDynamics.Traffic.SignalQueue.arrivalAverage_delay`: the arrival-average delay is
  `R ^ 2 * mu / (2 * (mu - lam) * (R + G))`.

## iii. Table of contents

- A. Cumulative counts of the signal queue
- B. Arrival volume, normalized area and the flow-pair bridge
- C. Occupancy identity and arrival-average delay

## iv. References

- J.-Y. Le Boudec and P. Thiran, *Network Calculus*, LNCS 2050, Section 1.1 (the virtual
  delay of a flow pair).
- Standard deterministic queueing at fixed-time signals (fluid model), e.g. D. Gazis (ed.),
  *Traffic Science*, 1974, as cited by `PhyslibExt.FluidDynamics.Traffic.SignalQueueArea`.

-/

open scoped NNReal ENNReal
open MeasureTheory Cslib.Algorithms.Networking.NetworkCalculus

@[expose] public section

namespace FluidDynamics.Traffic.SignalQueue

/-! ## A. Cumulative counts of the signal queue -/

/-- Cumulative arrivals by time `s`: `lam * s` vehicles at the constant arrival rate `lam`, as an
`ℝ≥0` count through `Real.toNNReal` (exact for `0 ≤ lam`). -/
noncomputable def arrivals (lam : ℝ) (s : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (lam * s)

/-- Cumulative departures by time `s` from the signal queue: the arrivals minus the vehicles
still queued, `lam * s - queueLen lam mu R s`, as an `ℝ≥0` count through `Real.toNNReal`
(exact on the admitted domain `0 < lam < mu`). -/
noncomputable def departures (lam mu R : ℝ) (s : ℝ≥0) : ℝ≥0 :=
  Real.toNNReal (lam * s - queueLen lam mu R s)

/-! ## B. Arrival volume, normalized area and the flow-pair bridge -/

/-- **Positive arrival volume.** For one clearing cycle (`0 < lam < mu`, `0 ≤ R`, `0 ≤ G` and
strict capacity `lam * (R + G) < mu * G`), the number of vehicles arriving in the cycle,
`lam * (R + G)`, is positive, because strict capacity forces a positive green time. The
cycle-average delay therefore never divides by zero. -/
lemma arrivalVolume_pos {lam mu R G : ℝ} (hlam : 0 < lam) (hmu : lam < mu) (hR : 0 ≤ R)
    (hG : 0 ≤ G) (hcap : lam * (R + G) < mu * G) :
    0 < lam * (R + G) := by
  have _ := hmu
  have hGpos : 0 < G := by
    rcases eq_or_lt_of_le hG with rfl | h
    · exfalso
      simp only [add_zero, mul_zero] at hcap
      have hnonneg : 0 ≤ lam * R := mul_nonneg hlam.le hR
      linarith
    · exact h
  have hRG : 0 < R + G := add_pos_of_nonneg_of_pos hR hGpos
  exact mul_pos hlam hRG

/-- **Normalized queue area.** For one clearing cycle, the queue area over `[0, R + G]` divided
by the arrival volume `lam * (R + G)` is `R ^ 2 * mu / (2 * (mu - lam) * (R + G))`, a time.
The area itself is the one-cycle area formula `queueLen_integral_cycle`. -/
lemma queueArea_div_arrivalVolume
    {lam mu R G : ℝ} (hlam : 0 < lam) (hmu : lam < mu) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hcap : lam * (R + G) < mu * G) :
    (∫ t in (0)..(R + G), queueLen lam mu R t) / (lam * (R + G))
      = R ^ 2 * mu / (2 * (mu - lam) * (R + G)) := by
  have hvol : 0 < lam * (R + G) := arrivalVolume_pos hlam hmu hR hG hcap
  have hRG : 0 < R + G := by
    by_contra h
    have hle0 : R + G ≤ 0 := le_of_not_gt h
    have hle : lam * (R + G) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.le hle0
    linarith
  rw [queueLen_integral_cycle hlam hmu hR hG hcap.le]
  have h1 : lam * (R + G) ≠ 0 := ne_of_gt hvol
  have h2 : mu - lam ≠ 0 := ne_of_gt (sub_pos.mpr hmu)
  have h3 : R + G ≠ 0 := ne_of_gt hRG
  have h2' : (2 : ℝ) * (mu - lam) ≠ 0 := mul_ne_zero (by norm_num) h2
  have h3' : (2 : ℝ) * (mu - lam) * (R + G) ≠ 0 := mul_ne_zero h2' h3
  field_simp

private lemma queueLen_le_aux {lam mu R : ℝ} (hlam : 0 < lam) (hmu : lam < mu)
    {t : ℝ} (ht : 0 ≤ t) : queueLen lam mu R t ≤ lam * t := by
  unfold queueLen
  split_ifs with h
  · exact le_rfl
  · rw [max_le_iff]
    refine ⟨mul_nonneg hlam.le ht, ?_⟩
    have hRt : R < t := lt_of_not_ge h
    have h1 : lam * R ≤ lam * t :=
      mul_le_mul_of_nonneg_left hRt.le hlam.le
    have h2 : 0 ≤ (mu - lam) * (t - R) :=
      mul_nonneg (sub_nonneg.mpr hmu.le) (sub_nonneg.mpr hRt.le)
    linarith

private lemma depInner_mono_aux {lam mu R : ℝ} (hlam : 0 < lam) (hmu : lam < mu) :
    Monotone (fun s : ℝ≥0 => lam * (s : ℝ) - queueLen lam mu R s) := by
  intro a b hab
  show lam * (a : ℝ) - queueLen lam mu R a ≤ lam * (b : ℝ) - queueLen lam mu R b
  have hxy : (a : ℝ) ≤ (b : ℝ) := NNReal.coe_le_coe.mpr hab
  have hy0 : 0 ≤ (b : ℝ) := b.coe_nonneg
  by_cases hxR : (a : ℝ) ≤ R
  · by_cases hyR : (b : ℝ) ≤ R
    · have e1 : queueLen lam mu R (a : ℝ) = lam * (a : ℝ) := by
        unfold queueLen
        rw [ite_eq_left hxR]
      have e2 : queueLen lam mu R (b : ℝ) = lam * (b : ℝ) := by
        unfold queueLen
        rw [ite_eq_left hyR]
      rw [e1, e2]
      linarith
    · have e1 : queueLen lam mu R (a : ℝ) = lam * (a : ℝ) := by
        unfold queueLen
        rw [ite_eq_left hxR]
      have e2 : queueLen lam mu R (b : ℝ)
          = max 0 (lam * R - (mu - lam) * ((b : ℝ) - R)) := by
        unfold queueLen
        rw [ite_eq_right hyR]
      rw [e1, e2]
      have hle : queueLen lam mu R (b : ℝ) ≤ lam * (b : ℝ) :=
        queueLen_le_aux hlam hmu hy0
      rw [e2] at hle
      linarith
  · by_cases hyR : (b : ℝ) ≤ R
    · exfalso
      exact hxR (le_trans hxy hyR)
    · have e1 : queueLen lam mu R (a : ℝ)
          = max 0 (lam * R - (mu - lam) * ((a : ℝ) - R)) := by
        unfold queueLen
        rw [ite_eq_right hxR]
      have e2 : queueLen lam mu R (b : ℝ)
          = max 0 (lam * R - (mu - lam) * ((b : ℝ) - R)) := by
        unfold queueLen
        rw [ite_eq_right hyR]
      rw [e1, e2]
      by_cases hga : lam * R - (mu - lam) * ((a : ℝ) - R) ≤ 0
      · by_cases hgb : lam * R - (mu - lam) * ((b : ℝ) - R) ≤ 0
        · rw [max_eq_left hga, max_eq_left hgb]
          have hle : lam * (a : ℝ) ≤ lam * (b : ℝ) :=
            mul_le_mul_of_nonneg_left hxy hlam.le
          linarith
        · exfalso
          have hgbpos : 0 < lam * R - (mu - lam) * ((b : ℝ) - R) :=
            not_le.mp hgb
          have hdiff : (lam * R - (mu - lam) * ((b : ℝ) - R))
              = (lam * R - (mu - lam) * ((a : ℝ) - R))
                - (mu - lam) * ((b : ℝ) - (a : ℝ)) := by
            ring
          have hprod : 0 ≤ (mu - lam) * ((b : ℝ) - (a : ℝ)) :=
            mul_nonneg (sub_nonneg.mpr hmu.le) (sub_nonneg.mpr hxy)
          linarith
      · by_cases hgb : lam * R - (mu - lam) * ((b : ℝ) - R) ≤ 0
        · rw [max_eq_right (le_of_not_ge hga), max_eq_left hgb]
          have hgapos : 0 < lam * R - (mu - lam) * ((a : ℝ) - R) :=
            not_le.mp hga
          have hprod : 0 ≤ lam * ((b : ℝ) - (a : ℝ)) :=
            mul_nonneg hlam.le (sub_nonneg.mpr hxy)
          have hexpand : lam * ((b : ℝ) - (a : ℝ)) = lam * b - lam * a := by
            ring
          linarith
        · rw [max_eq_right (le_of_not_ge hga), max_eq_right (le_of_not_ge hgb)]
          have hdiff : (lam * R - (mu - lam) * ((a : ℝ) - R))
              - (lam * R - (mu - lam) * ((b : ℝ) - R))
              = (mu - lam) * ((b : ℝ) - (a : ℝ)) := by
            ring
          have hprod : 0 ≤ (mu - lam) * ((b : ℝ) - (a : ℝ)) :=
            mul_nonneg (sub_nonneg.mpr hmu.le) (sub_nonneg.mpr hxy)
          have hprod2 : 0 ≤ lam * ((b : ℝ) - (a : ℝ)) :=
            mul_nonneg hlam.le (sub_nonneg.mpr hxy)
          have hexpand : lam * ((b : ℝ) - (a : ℝ)) = lam * b - lam * a := by
            ring
          linarith

/-- **Flow-pair bridge.** On the admitted domain `0 < lam < mu`, `0 ≤ R`, the cumulative
arrivals and departures of the signal queue form a lossless flow pair (both vanish at time `0`,
both are nondecreasing, and departures never exceed arrivals), and the backlog of that pair at
every time `s ≥ 0` is the queue length `queueLen lam mu R s`. It identifies the fluid queue with
its cumulative-count description, the form the virtual delay is defined on. -/
lemma isFlowPair_and_backlog_eq_queueLen {lam mu R : ℝ} (hlam : 0 < lam) (hmu : lam < mu)
    (hR : 0 ≤ R) :
    IsFlowPair (arrivals lam) (departures lam mu R) ∧
      ∀ s : ℝ≥0, backlog (arrivals lam) (departures lam mu R) s
        = ENNReal.ofReal (queueLen lam mu R s) := by
  have hAmono : Monotone (arrivals lam) := by
    intro a b hab
    have hle : lam * (a : ℝ) ≤ lam * (b : ℝ) :=
      mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hab) hlam.le
    unfold arrivals
    exact Real.toNNReal_le_toNNReal hle
  have hA0 : arrivals lam 0 = 0 := by
    unfold arrivals
    simp
  have hDmono : Monotone (departures lam mu R) := by
    intro a b hab
    have hle : lam * (a : ℝ) - queueLen lam mu R (a : ℝ)
        ≤ lam * (b : ℝ) - queueLen lam mu R (b : ℝ) :=
      depInner_mono_aux hlam hmu hab
    unfold departures
    exact Real.toNNReal_le_toNNReal hle
  have hD0 : departures lam mu R 0 = 0 := by
    unfold departures queueLen
    rw [NNReal.coe_zero, ite_eq_left hR]
    simp
  have hle : ∀ t, departures lam mu R t ≤ arrivals lam t := by
    intro t
    have hQ0 : 0 ≤ queueLen lam mu R (t : ℝ) :=
      queueLen_nonneg hlam t.coe_nonneg
    unfold departures arrivals
    apply Real.toNNReal_le_toNNReal
    linarith
  constructor
  · unfold IsFlowPair IsCumulativeFlow
    exact ⟨⟨hAmono, hA0⟩, ⟨hDmono, hD0⟩, hle⟩
  · intro s
    have hQle : queueLen lam mu R (s : ℝ) ≤ lam * (s : ℝ) :=
      queueLen_le_aux hlam hmu s.coe_nonneg
    have hD0 : 0 ≤ lam * (s : ℝ) - queueLen lam mu R (s : ℝ) := by
      linarith
    unfold backlog arrivals departures
    rw [ENNReal.ofNNReal_toNNReal, ENNReal.ofNNReal_toNNReal]
    rw [← ENNReal.ofReal_sub _ hD0]
    congr 1
    ring

private lemma tc_nonneg {lam mu R : ℝ} (hlam : 0 < lam) (hmu : lam < mu)
    (hR : 0 ≤ R) : 0 ≤ mu * R / (mu - lam) :=
  div_nonneg (mul_nonneg (le_of_lt (lt_trans hlam hmu)) hR)
    (le_of_lt (sub_pos.mpr hmu))

private lemma tc_eq {lam mu R : ℝ} (hmu : lam < mu) :
    mu * R / (mu - lam) = R + lam * R / (mu - lam) := by
  have hdm0 : mu - lam ≠ 0 := ne_of_gt (sub_pos.mpr hmu)
  field_simp
  ring

private lemma tc_lt_cycle {lam mu R G : ℝ} (hmu : lam < mu)
    (hcap : lam * (R + G) < mu * G) : mu * R / (mu - lam) < R + G := by
  have hdm_pos : 0 < mu - lam := sub_pos.mpr hmu
  rw [tc_eq hmu]
  have h2 : lam * R / (mu - lam) < G := by
    rw [div_lt_iff₀ hdm_pos]
    linarith [hcap]
  linarith

private lemma tc_ge_R {lam mu R : ℝ} (hlam : 0 < lam) (hmu : lam < mu)
    (hR : 0 ≤ R) : R ≤ mu * R / (mu - lam) := by
  rw [tc_eq hmu]
  have hnn : 0 ≤ lam * R / (mu - lam) :=
    div_nonneg (mul_nonneg hlam.le hR) (sub_pos.mpr hmu).le
  linarith

private lemma delayExpr_mu_mul {lam mu R s : ℝ} (hlam : 0 < lam) (hmu : lam < mu) :
    mu * (R + lam * s / mu - s) = mu * R - (mu - lam) * s := by
  have hmu0 : mu ≠ 0 := ne_of_gt (lt_trans hlam hmu)
  field_simp
  ring

private lemma delay_le_of_mem {R R' : ℝ≥0 → ℝ≥0} {t τ : ℝ≥0}
    (h : R t ≤ R' (t + τ)) : delay R R' t ≤ (τ : ℝ≥0∞) := by
  have h1 : (⨅ u : {τ' : ℝ≥0 // R t ≤ R' (t + τ')}, ((u.val : ℝ≥0) : ℝ≥0∞))
      ≤ (τ : ℝ≥0∞) :=
    iInf_le (fun u : {τ' : ℝ≥0 // R t ≤ R' (t + τ')} => ((u.val : ℝ≥0) : ℝ≥0∞))
      ⟨τ, h⟩
  exact h1

private lemma le_delay_of_forall {R R' : ℝ≥0 → ℝ≥0} {t : ℝ≥0} {c : ℝ≥0∞}
    (h : ∀ τ : ℝ≥0, R t ≤ R' (t + τ) → c ≤ (τ : ℝ≥0∞)) : c ≤ delay R R' t := by
  unfold delay
  apply le_iInf
  intro u
  obtain ⟨τ, hτ⟩ := u
  exact h τ hτ

private lemma delay_eval_mem {lam mu R : ℝ} (hlam : 0 < lam) (hmu : lam < mu)
    (hR : 0 ≤ R) {s : ℝ} (hs0 : 0 < s) :
    delay (arrivals lam) (departures lam mu R) s.toNNReal
      = ENNReal.ofReal (max 0 (R + lam * s / mu - s)) := by
  have hdm_pos : 0 < mu - lam := sub_pos.mpr hmu
  have hmu_pos : 0 < mu := lt_trans hlam hmu
  have htcoe : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs0.le
  by_cases hs_tc : s ≤ mu * R / (mu - lam)
  · have h1 : s * (mu - lam) ≤ mu * R := (le_div_iff₀ hdm_pos).mp hs_tc
    have hc : 0 ≤ R + lam * s / mu - s := by
      have hmc := delayExpr_mu_mul hlam hmu (R := R) (s := s)
      have hnn : 0 ≤ mu * (R + lam * s / mu - s) := by
        rw [hmc]
        linarith [h1]
      by_contra hneg
      have hneg' : R + lam * s / mu - s < 0 := lt_of_not_ge hneg
      have hneg'' : mu * (R + lam * s / mu - s) < 0 :=
        mul_neg_of_pos_of_neg hmu_pos hneg'
      linarith
    rw [max_eq_right hc]
    apply le_antisymm
    · have hcoe : ((s.toNNReal + Real.toNNReal (R + lam * s / mu - s) : ℝ≥0) : ℝ)
          = R + lam * s / mu := by
        rw [NNReal.coe_add, Real.coe_toNNReal s hs0.le, Real.coe_toNNReal _ hc]
        exact add_sub_cancel s (R + lam * s / mu)
      have hpos : 0 < lam * s / mu := div_pos (mul_pos hlam hs0) hmu_pos
      have hgt : ¬ R + lam * s / mu ≤ R := by
        intro h
        linarith [hpos]
      have hg : lam * R - (mu - lam) * ((R + lam * s / mu) - R)
          = lam * (R + lam * s / mu - s) := by
        have hmu0 : mu ≠ 0 := ne_of_gt hmu_pos
        field_simp
        ring
      have hQsc : queueLen lam mu R (R + lam * s / mu)
          = lam * (R + lam * s / mu - s) := by
        unfold queueLen
        rw [ite_eq_right hgt, hg, max_eq_right (mul_nonneg hlam.le hc)]
      have hDval : lam * ((s.toNNReal + Real.toNNReal (R + lam * s / mu - s) : ℝ≥0):ℝ)
          - queueLen lam mu R
            ((s.toNNReal + Real.toNNReal (R + lam * s / mu - s) : ℝ≥0):ℝ)
          = lam * s := by
        rw [hcoe, hQsc]
        have hmu0 : mu ≠ 0 := ne_of_gt hmu_pos
        field_simp
        ring
      have hDeq : departures lam mu R (s.toNNReal + Real.toNNReal (R + lam * s / mu - s))
          = arrivals lam s.toNNReal := by
        unfold departures arrivals
        rw [htcoe, hDval]
      have hcond : arrivals lam s.toNNReal
          ≤ departures lam mu R (s.toNNReal + Real.toNNReal (R + lam * s / mu - s)) :=
        hDeq.ge
      have hub := delay_le_of_mem hcond
      rw [ENNReal.ofNNReal_toNNReal] at hub
      exact hub
    · apply le_delay_of_forall
      intro τ hτ
      have hcoe : ((s.toNNReal + τ : ℝ≥0) : ℝ) = s + (τ : ℝ) := by
        rw [NNReal.coe_add, Real.coe_toNNReal s hs0.le]
      have hQle : queueLen lam mu R ((s.toNNReal + τ : ℝ≥0):ℝ)
          ≤ lam * ((s.toNNReal + τ : ℝ≥0):ℝ) :=
        queueLen_le_aux hlam hmu (s.toNNReal + τ).coe_nonneg
      have harg : 0 ≤ lam * ((s.toNNReal + τ : ℝ≥0):ℝ)
          - queueLen lam mu R ((s.toNNReal + τ : ℝ≥0):ℝ) := by
        linarith
      have hτ' : Real.toNNReal (lam * ((s.toNNReal : ℝ≥0):ℝ))
          ≤ Real.toNNReal (lam * ((s.toNNReal + τ : ℝ≥0):ℝ)
            - queueLen lam mu R ((s.toNNReal + τ : ℝ≥0):ℝ)) := hτ
      have hreal := (Real.toNNReal_le_toNNReal_iff harg).mp hτ'
      rw [htcoe, hcoe] at hreal
      have hQv : queueLen lam mu R (s + (τ:ℝ)) ≤ lam * (τ:ℝ) := by
        linarith [hreal]
      by_cases hvR : s + (τ:ℝ) ≤ R
      · exfalso
        have hQe : queueLen lam mu R (s + (τ:ℝ)) = lam * (s + (τ:ℝ)) := by
          unfold queueLen
          rw [ite_eq_left hvR]
        rw [hQe] at hQv
        have hpos : 0 < lam * s := mul_pos hlam hs0
        linarith
      · have hQe : queueLen lam mu R (s + (τ:ℝ))
            = max 0 (lam * R - (mu - lam) * ((s + (τ:ℝ)) - R)) := by
          unfold queueLen
          rw [ite_eq_right hvR]
        rw [hQe] at hQv
        have hg : lam * R - (mu - lam) * ((s + (τ:ℝ)) - R) ≤ lam * (τ:ℝ) :=
          le_trans (le_max_right _ _) hQv
        have hmc := delayExpr_mu_mul hlam hmu (R := R) (s := s)
        have hle : mu * (R + lam * s / mu - s) ≤ mu * (τ:ℝ) := by
          rw [hmc]
          linarith [hg]
        have hcU : R + lam * s / mu - s ≤ (τ:ℝ) :=
          le_of_mul_le_mul_left hle hmu_pos
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal hcU
  · have hs_tc' : mu * R / (mu - lam) < s := not_le.mp hs_tc
    have h1 : mu * R < s * (mu - lam) := (div_lt_iff₀ hdm_pos).mp hs_tc'
    have hc : R + lam * s / mu - s < 0 := by
      have hmc := delayExpr_mu_mul hlam hmu (R := R) (s := s)
      have hneg : mu * (R + lam * s / mu - s) < 0 := by
        rw [hmc]
        linarith [h1]
      by_contra hcon
      have hnn : 0 ≤ R + lam * s / mu - s := le_of_not_gt hcon
      have hnn' : 0 ≤ mu * (R + lam * s / mu - s) :=
        mul_nonneg hmu_pos.le hnn
      linarith
    rw [max_eq_left (le_of_lt hc), ENNReal.ofReal_zero]
    apply le_antisymm
    · have hRlt : R < s := lt_of_le_of_lt (tc_ge_R hlam hmu hR) hs_tc'
      have hgneg : lam * R - (mu - lam) * (s - R) < 0 := by
        linarith [h1]
      have hQs : queueLen lam mu R s = 0 := by
        unfold queueLen
        rw [ite_eq_right (not_le_of_gt hRlt), max_eq_left (le_of_lt hgneg)]
      have hcoe0 : ((s.toNNReal + 0 : ℝ≥0):ℝ) = s := by
        rw [NNReal.coe_add, htcoe, NNReal.coe_zero, add_zero]
      have hDeq : departures lam mu R (s.toNNReal + 0) = arrivals lam s.toNNReal := by
        unfold departures arrivals
        rw [hcoe0, hQs, sub_zero, htcoe]
      have h0mem : arrivals lam s.toNNReal ≤ departures lam mu R (s.toNNReal + 0) :=
        hDeq.ge
      have hub := delay_le_of_mem h0mem
      rw [ENNReal.coe_zero] at hub
      exact hub
    · exact zero_le

private lemma linear_integral {R lam mu tc : ℝ} :
    ∫ x in (0:ℝ)..tc, (R + lam * x / mu - x) ∂volume
      = R * tc + (lam * (tc ^ 2 / 2) / mu) - tc ^ 2 / 2 := by
  have h1 : IntervalIntegrable (fun x : ℝ => x) volume 0 tc :=
    continuous_id.intervalIntegrable 0 tc
  have hid : (∫ x in (0:ℝ)..tc, x ∂volume) = tc ^ 2 / 2 := by
    rw [integral_id]
    ring
  have hR : IntervalIntegrable (fun _ : ℝ => R) volume 0 tc :=
    continuous_const.intervalIntegrable 0 tc
  have hF2 : IntervalIntegrable (fun x : ℝ => lam * x / mu) volume 0 tc :=
    ((continuous_const.mul continuous_id).div_const mu).intervalIntegrable 0 tc
  have hF1 : IntervalIntegrable (fun x : ℝ => R + lam * x / mu) volume 0 tc :=
    (continuous_const.add ((continuous_const.mul continuous_id).div_const mu)).intervalIntegrable
      0 tc
  have hsub : (∫ x in (0:ℝ)..tc, (R + lam * x / mu - x) ∂volume)
      = (∫ x in (0:ℝ)..tc, (R + lam * x / mu) ∂volume) - ∫ x in (0:ℝ)..tc, x ∂volume :=
    intervalIntegral.integral_sub hF1 h1
  have hadd : (∫ x in (0:ℝ)..tc, (R + lam * x / mu) ∂volume)
      = (∫ _ in (0:ℝ)..tc, R ∂volume) + ∫ x in (0:ℝ)..tc, (lam * x / mu) ∂volume :=
    intervalIntegral.integral_add hR hF2
  have hRval : (∫ _ in (0:ℝ)..tc, R ∂volume) = R * tc := by
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    ring
  have hdiv : (∫ x in (0:ℝ)..tc, (lam * x / mu) ∂volume)
      = (∫ x in (0:ℝ)..tc, (lam * x) ∂volume) / mu :=
    intervalIntegral.integral_div mu (fun x : ℝ => lam * x)
  have hmul : (∫ x in (0:ℝ)..tc, (lam * x) ∂volume) = lam * (tc ^ 2 / 2) := by
    have h2 : (∫ x in (0:ℝ)..tc, (lam * x) ∂volume)
        = lam * (∫ x in (0:ℝ)..tc, x ∂volume) :=
      intervalIntegral.integral_const_mul lam (fun x : ℝ => x)
    rw [hid] at h2
    exact h2
  rw [hsub, hadd, hRval, hdiv, hmul, hid]

/-! ## C. Occupancy identity and arrival-average delay -/

/-- **Occupancy identity for the cycle.** For one clearing cycle, the virtual delay of each
vehicle arriving in `[0, R + G)`, integrated against the arrival measure
`ENNReal.ofReal lam • volume`, equals the queue area over `[0, R + G]`: the total waiting of the
vehicles that arrive in the cycle is the time integral of the queue length. The area itself is
the one-cycle area formula `queueLen_integral_cycle`. -/
theorem arrivalWeighted_delay_eq_queueArea
    {lam mu R G : ℝ} (hlam : 0 < lam) (hmu : lam < mu) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hcap : lam * (R + G) < mu * G) :
    ∫⁻ s in Set.Ico 0 (R + G), delay (arrivals lam) (departures lam mu R) s.toNNReal
        ∂(ENNReal.ofReal lam • volume)
      = ENNReal.ofReal (∫ t in (0)..(R + G), queueLen lam mu R t) := by
  have hdm_pos : 0 < mu - lam := sub_pos.mpr hmu
  have hmu_pos : 0 < mu := lt_trans hlam hmu
  have htc0 : 0 ≤ mu * R / (mu - lam) := tc_nonneg hlam hmu hR
  have htc1 : mu * R / (mu - lam) < R + G := tc_lt_cycle hmu hcap
  have hRGpos : 0 < R + G := lt_of_le_of_lt htc0 htc1
  have h0 : ∀ᵐ s ∂(ENNReal.ofReal lam • volume), s ≠ (0:ℝ) := by
    apply MeasureTheory.Measure.ae_smul_measure _ (ENNReal.ofReal lam)
    rw [MeasureTheory.ae_iff]
    have hset : {s : ℝ | ¬ s ≠ 0} = {(0:ℝ)} := by ext x; simp
    rw [hset]
    exact Real.volume_singleton
  have hae : (fun s : ℝ => delay (arrivals lam) (departures lam mu R) s.toNNReal)
      =ᵐ[(ENNReal.ofReal lam • volume).restrict (Set.Ico 0 (R + G))]
      (fun s => ENNReal.ofReal (max 0 (R + lam * s / mu - s))) := by
    apply (MeasureTheory.ae_restrict_iff' measurableSet_Ico).mpr
    filter_upwards [h0] with s hs hmem
    obtain ⟨hs0, _hs1⟩ := Set.mem_Ico.mp hmem
    have hspos : 0 < s := lt_of_le_of_ne hs0 (Ne.symm hs)
    exact delay_eval_mem hlam hmu hR hspos
  rw [MeasureTheory.lintegral_congr_ae hae]
  rw [MeasureTheory.setLIntegral_smul_measure, smul_eq_mul]
  have hFcont : Continuous (fun s : ℝ => R + lam * s / mu - s) :=
    (continuous_const.add ((continuous_const.mul continuous_id).div_const mu)).sub
      continuous_id
  have hg_cont : Continuous (fun s : ℝ => max 0 (R + lam * s / mu - s)) :=
    continuous_const.max hFcont
  have hg_int : Integrable (fun s : ℝ => max 0 (R + lam * s / mu - s))
      (volume.restrict (Set.Ico 0 (R + G))) := by
    have hsub : Set.Ico 0 (R + G) ⊆ Set.Icc 0 (R + G) := Set.Ico_subset_Icc_self
    have hintcc := hg_cont.integrableOn_Icc (a := 0) (b := R + G) (μ := volume)
    exact hintcc.mono_set hsub
  have hg_nn : 0 ≤ᵐ[volume.restrict (Set.Ico 0 (R + G))]
      (fun s : ℝ => max 0 (R + lam * s / mu - s)) := by
    apply Filter.Eventually.of_forall
    intro s
    exact le_max_left 0 _
  have hconv : ENNReal.ofReal (∫ s in Set.Ico 0 (R + G), max 0 (R + lam * s / mu - s) ∂volume)
      = ∫⁻ s in Set.Ico 0 (R + G), ENNReal.ofReal (max 0 (R + lam * s / mu - s)) ∂volume :=
    MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg_int hg_nn
  rw [← hconv]
  rw [← ENNReal.ofReal_mul hlam.le]
  congr 1
  rw [queueLen_integral_cycle hlam hmu hR hG hcap.le]
  have hIcoIoc : (Set.Ico 0 (R + G)) =ᵐ[volume] (Set.Ioc 0 (R + G)) :=
    MeasureTheory.Ico_ae_eq_Ioc
  have hrestr : volume.restrict (Set.Ico 0 (R + G))
      = volume.restrict (Set.Ioc 0 (R + G)) :=
    MeasureTheory.Measure.restrict_congr_set hIcoIoc
  have hIco_eq_Ioc : (∫ s in Set.Ico 0 (R + G), max 0 (R + lam * s / mu - s) ∂volume)
      = ∫ s in Set.Ioc 0 (R + G), max 0 (R + lam * s / mu - s) ∂volume := by
    rw [hrestr]
  have hIoc_eq_int : (∫ s in Set.Ioc 0 (R + G), max 0 (R + lam * s / mu - s) ∂volume)
      = ∫ t in (0:ℝ)..(R + G), max 0 (R + lam * t / mu - t) ∂volume :=
    (intervalIntegral.integral_of_le hRGpos.le).symm
  have hg_int01 : IntervalIntegrable (fun s : ℝ => max 0 (R + lam * s / mu - s)) volume 0
      (mu * R / (mu - lam)) :=
    hg_cont.intervalIntegrable 0 _
  have hg_int12 : IntervalIntegrable (fun s : ℝ => max 0 (R + lam * s / mu - s)) volume
      (mu * R / (mu - lam)) (R + G) :=
    hg_cont.intervalIntegrable _ _
  have hsplit : (∫ t in (0:ℝ)..(R + G), max 0 (R + lam * t / mu - t) ∂volume)
      = (∫ t in (0:ℝ)..(mu * R / (mu - lam)), max 0 (R + lam * t / mu - t) ∂volume)
        + ∫ t in (mu * R / (mu - lam))..(R + G), max 0 (R + lam * t / mu - t) ∂volume :=
    (intervalIntegral.integral_add_adjacent_intervals hg_int01 hg_int12).symm
  have hpiece1 : (∫ t in (0:ℝ)..(mu * R / (mu - lam)), max 0 (R + lam * t / mu - t) ∂volume)
      = ∫ t in (0:ℝ)..(mu * R / (mu - lam)), (R + lam * t / mu - t) ∂volume := by
    apply intervalIntegral.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le htc0] at hx
    obtain ⟨_, hx1⟩ := Set.mem_Ioc.mp hx
    have h1x : x * (mu - lam) ≤ mu * R := (le_div_iff₀ hdm_pos).mp hx1
    have hnn : 0 ≤ R + lam * x / mu - x := by
      have hmc := delayExpr_mu_mul hlam hmu (R := R) (s := x)
      have hnn' : 0 ≤ mu * (R + lam * x / mu - x) := by
        rw [hmc]
        linarith [h1x]
      by_contra hneg
      have hneg' : R + lam * x / mu - x < 0 := lt_of_not_ge hneg
      have hneg'' : mu * (R + lam * x / mu - x) < 0 :=
        mul_neg_of_pos_of_neg hmu_pos hneg'
      linarith
    exact max_eq_right hnn
  have hpiece2 : (∫ t in (mu * R / (mu - lam))..(R + G),
        max 0 (R + lam * t / mu - t) ∂volume) = 0 := by
    have hcongr : (∫ t in (mu * R / (mu - lam))..(R + G),
          max 0 (R + lam * t / mu - t) ∂volume)
        = ∫ _ in (mu * R / (mu - lam))..(R + G), (0:ℝ) ∂volume := by
      apply intervalIntegral.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x hx
      rw [Set.uIoc_of_le htc1.le] at hx
      obtain ⟨hx0, _⟩ := Set.mem_Ioc.mp hx
      have hneg : R + lam * x / mu - x ≤ 0 := by
        have h1x : mu * R ≤ x * (mu - lam) := (div_le_iff₀ hdm_pos).mp hx0.le
        have hmc := delayExpr_mu_mul hlam hmu (R := R) (s := x)
        have hle : mu * (R + lam * x / mu - x) ≤ 0 := by
          rw [hmc]
          linarith [h1x]
        by_contra hcon
        have hpos : 0 < R + lam * x / mu - x := lt_of_not_ge hcon
        have hpos' : 0 < mu * (R + lam * x / mu - x) := mul_pos hmu_pos hpos
        linarith
      exact max_eq_left hneg
    rw [hcongr]
    exact intervalIntegral.integral_zero
  have hlin : (∫ t in (0:ℝ)..(mu * R / (mu - lam)), (R + lam * t / mu - t) ∂volume)
      = R * (mu * R / (mu - lam)) + (lam * ((mu * R / (mu - lam)) ^ 2 / 2) / mu)
        - (mu * R / (mu - lam)) ^ 2 / 2 :=
    linear_integral
  rw [hIco_eq_Ioc, hIoc_eq_int, hsplit, hpiece1, hpiece2, add_zero, hlin]
  have hdm0 : mu - lam ≠ 0 := ne_of_gt hdm_pos
  have hmu0 : mu ≠ 0 := ne_of_gt hmu_pos
  field_simp
  ring

/-- **Arrival-average delay.** For one clearing cycle, the arrival-weighted virtual delay over
`[0, R + G)` divided by the arrival volume `lam * (R + G)` is
`R ^ 2 * mu / (2 * (mu - lam) * (R + G))`: the normalized queue area is the mean
first-in-first-out delay of the vehicles arriving in the cycle. The area enters through the
one-cycle area formula `queueLen_integral_cycle`. -/
theorem arrivalAverage_delay
    {lam mu R G : ℝ} (hlam : 0 < lam) (hmu : lam < mu) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hcap : lam * (R + G) < mu * G) :
    (∫⁻ s in Set.Ico 0 (R + G), delay (arrivals lam) (departures lam mu R) s.toNNReal
        ∂(ENNReal.ofReal lam • volume)) / ENNReal.ofReal (lam * (R + G))
      = ENNReal.ofReal (R ^ 2 * mu / (2 * (mu - lam) * (R + G))) := by
  rw [arrivalWeighted_delay_eq_queueArea hlam hmu hR hG hcap]
  rw [queueLen_integral_cycle hlam hmu hR hG hcap.le]
  have hvol : 0 < lam * (R + G) := arrivalVolume_pos hlam hmu hR hG hcap
  rw [← ENNReal.ofReal_div_of_pos hvol]
  congr 1
  have hRG : 0 < R + G := by
    by_contra h
    have hle0 : R + G ≤ 0 := le_of_not_gt h
    have hle : lam * (R + G) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam.le hle0
    linarith
  have h1 : lam * (R + G) ≠ 0 := ne_of_gt hvol
  have h2 : mu - lam ≠ 0 := ne_of_gt (sub_pos.mpr hmu)
  have h3 : R + G ≠ 0 := ne_of_gt hRG
  have h2' : (2 : ℝ) * (mu - lam) ≠ 0 := mul_ne_zero (by norm_num) h2
  have h3' : (2 : ℝ) * (mu - lam) * (R + G) ≠ 0 := mul_ne_zero h2' h3
  field_simp

end FluidDynamics.Traffic.SignalQueue
