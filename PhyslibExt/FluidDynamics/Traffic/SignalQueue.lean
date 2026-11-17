/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.ContinuousOn

/-!
# Signal-queue clearing witness

## i. Overview

The deterministic fluid queue at a traffic signal over one cycle
(the one-cycle, non-periodic fluid model): queue grows at arrival
rate during red, drains at `mu - lam` during green, clears at
`R + lam * R / (mu - lam)`, and is empty at the cycle end under the
capacity condition. Times beyond the cycle end belong to the next
cycle of a periodic signal, which this one-cycle model does not
describe; here the queue simply remains at its cleared value.

## ii. Key results

- `FluidDynamics.Traffic.SignalQueue.queueLen_cycle_end`: empty at
  the cycle end.
- `FluidDynamics.Traffic.SignalQueue.queueLen_eq_zero_of_clearance`:
  clearance offset.
- Rate laws on red, green, and after clearance.

## iii. Table of contents

- A. The queue witness

## iv. References

- Standard deterministic queueing at fixed-time signals (fluid
  model), e.g. D. Gazis (ed.), *Traffic Science*, 1974.

## A. The queue witness
-/

@[expose] public section

namespace FluidDynamics.Traffic.SignalQueue

/-- Deterministic fluid queue over one signal cycle: arrival rate
`lam`, service rate `mu`, red `R`, green `G`, cycle `C = R + G`.
Queue grows at rate `lam` during red and drains at rate `mu - lam`
during green until it clears. -/
noncomputable def queueLen (lam mu R : ℝ) (t : ℝ) : ℝ :=
  if t ≤ R then lam * t
  else max 0 (lam * R - (mu - lam) * (t - R))

/-- The queue starts empty. -/
theorem queueLen_zero {lam mu R : ℝ} (hR : 0 ≤ R) :
    queueLen lam mu R 0 = 0 := by
  unfold queueLen
  rw [ite_eq_left hR, mul_zero]

/-- The queue is empty at the cycle end, under
`lam * (R + G) ≤ mu * G` with `0 < lam < mu`. -/
theorem queueLen_cycle_end {lam mu R G : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hcap : lam * (R + G) ≤ mu * G) :
    queueLen lam mu R (R + G) = 0 := by
  have _ : lam < mu := hmu
  unfold queueLen
  by_cases h : R + G ≤ R
  · rw [ite_eq_left h]
    have hG0 : G = 0 := by linarith [hG, h]
    have hmu0 : mu * G = 0 := by rw [hG0, mul_zero]
    have hcap0 : lam * (R + G) ≤ 0 := by
      rw [hmu0] at hcap
      exact hcap
    have hnn : 0 ≤ lam * (R + G) := by
      rw [hG0, add_zero]
      exact mul_nonneg (le_of_lt hlam) hR
    exact le_antisymm hcap0 hnn
  · rw [ite_eq_right h]
    apply max_eq_left
    have hcap' : lam * R ≤ (mu - lam) * G := by
      have hmul := hcap
      rw [mul_add] at hmul
      have heq : (mu - lam) * G = mu * G - lam * G := by ring
      linarith [hmul, heq]
    have hsub : R + G - R = G := by ring
    rw [hsub]
    linarith [hcap']

/-- Clearance offset: the queue is zero from time
`R + lam * R / (mu - lam)` onward. -/
theorem queueLen_eq_zero_of_clearance {lam mu R : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) {t : ℝ}
    (ht : R + lam * R / (mu - lam) ≤ t) :
    queueLen lam mu R t = 0 := by
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have hlamR : 0 ≤ lam * R := mul_nonneg (le_of_lt hlam) hR
  have hdiv : 0 ≤ lam * R / (mu - lam) := div_nonneg hlamR (le_of_lt hpos)
  unfold queueLen
  by_cases h : t ≤ R
  · rw [ite_eq_left h]
    have hle : lam * R / (mu - lam) ≤ 0 := by linarith [ht, h]
    have hdiv0 : lam * R / (mu - lam) = 0 := le_antisymm hle hdiv
    have hlamR0 : lam * R = 0 :=
      (div_eq_zero_iff.mp hdiv0).resolve_right (ne_of_gt hpos)
    have hR0 : R = 0 :=
      (mul_eq_zero.mp hlamR0).resolve_left (ne_of_gt hlam)
    have ht0 : t = 0 := by
      have h1 : t ≤ 0 := by
        have h' := h
        rw [hR0] at h'
        exact h'
      have h2 : 0 ≤ t := by
        have h' := ht
        rw [hdiv0, hR0] at h'
        linarith
      linarith
    rw [ht0, mul_zero]
  · rw [ite_eq_right h]
    apply max_eq_left
    have h1 : lam * R / (mu - lam) ≤ t - R := by linarith [ht]
    rw [div_le_iff₀ hpos] at h1
    have h2 : (t - R) * (mu - lam) = (mu - lam) * (t - R) := by ring
    rw [h2] at h1
    linarith

/-- Nonnegativity everywhere in time. -/
theorem queueLen_nonneg {lam mu R : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ queueLen lam mu R t := by
  unfold queueLen
  by_cases h : t ≤ R
  · rw [ite_eq_left h]
    exact mul_nonneg (le_of_lt hlam) ht0
  · rw [ite_eq_right h]
    exact le_max_left 0 _

/-- Continuity on the cycle interval `[0, R + G]`. -/
theorem queueLen_continuousOn {lam mu R G : ℝ} (hlam : 0 ≤ lam)
    (hR : 0 ≤ R) (hG : 0 ≤ G) :
    ContinuousOn (queueLen lam mu R) (Set.Icc 0 (R + G)) := by
  have _ : 0 ≤ G := hG
  have hlamR : 0 ≤ lam * R := mul_nonneg hlam hR
  have hcont : Continuous (queueLen lam mu R) := by
    unfold queueLen
    apply Continuous.if_le
    · fun_prop
    · fun_prop
    · exact continuous_id'
    · exact continuous_const
    · intro x hx
      change x = R at hx
      subst hx
      rw [sub_self, mul_zero, sub_zero]
      exact (max_eq_right hlamR).symm
  exact hcont.continuousOn

/-- Red-phase rate: inside the red phase the queue derivative is
the arrival rate. -/
theorem queueLen_deriv_red {lam mu R t : ℝ} (ht : t < R) :
    deriv (queueLen lam mu R) t = lam := by
  have heq : Filter.EventuallyEq (nhds t) (queueLen lam mu R)
      (fun s => lam * s) := by
    filter_upwards [Iio_mem_nhds ht] with s hs
    unfold queueLen
    rw [ite_eq_left (le_of_lt hs)]
  rw [heq.deriv_eq]
  have hder : HasDerivAt (fun s : ℝ => lam * s) (lam * 1) t :=
    HasDerivAt.const_mul lam (hasDerivAt_id' t)
  rw [hder.deriv, mul_one]

/-- Green-phase rate before clearance: the derivative is
`-(mu - lam)`. -/
theorem queueLen_deriv_green {lam mu R G t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (htR : R < t)
    (htc : t < R + lam * R / (mu - lam)) (htG : t < R + G) :
    deriv (queueLen lam mu R) t = -(mu - lam) := by
  have _ : 0 < lam := hlam
  have _ : t < R + G := htG
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have heq : Filter.EventuallyEq (nhds t) (queueLen lam mu R)
      (fun s => lam * R - (mu - lam) * (s - R)) := by
    filter_upwards [Ioi_mem_nhds htR, Iio_mem_nhds htc] with s hsR hsc
    have hsR' : R < s := hsR
    have hsc' : s < R + lam * R / (mu - lam) := hsc
    unfold queueLen
    rw [ite_eq_right (not_le_of_gt hsR')]
    have hX : 0 ≤ lam * R - (mu - lam) * (s - R) := by
      have h1 : s - R < lam * R / (mu - lam) := by linarith [hsc']
      rw [lt_div_iff₀ hpos] at h1
      have h2 : (s - R) * (mu - lam) = (mu - lam) * (s - R) := by ring
      rw [h2] at h1
      linarith
    rw [max_eq_right hX]
  rw [heq.deriv_eq]
  have h2 : HasDerivAt (fun s : ℝ => (mu - lam) * (s - R))
      ((mu - lam) * 1) t :=
    HasDerivAt.const_mul (mu - lam) ((hasDerivAt_id' t).sub_const R)
  have h3 : HasDerivAt (fun s : ℝ => lam * R - (mu - lam) * (s - R))
      (-((mu - lam) * 1)) t :=
    HasDerivAt.const_sub (lam * R) h2
  rw [h3.deriv]
  ring

/-- After clearance the queue stays at zero: derivative `0`. -/
theorem queueLen_deriv_after_clearance {lam mu R G t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) (htG : t ≤ R + G)
    (ht : R + lam * R / (mu - lam) < t) :
    deriv (queueLen lam mu R) t = 0 := by
  have _ : t ≤ R + G := htG
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have hlamR : 0 ≤ lam * R := mul_nonneg (le_of_lt hlam) hR
  have hdiv : 0 ≤ lam * R / (mu - lam) := div_nonneg hlamR (le_of_lt hpos)
  have htcR : R ≤ R + lam * R / (mu - lam) := by linarith [hdiv]
  have heq : Filter.EventuallyEq (nhds t) (queueLen lam mu R)
      (fun _ => 0) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    have hs' : R + lam * R / (mu - lam) < s := hs
    unfold queueLen
    by_cases h : s ≤ R
    · exfalso
      linarith [h, htcR, hs']
    · rw [ite_eq_right h]
      have hX : lam * R - (mu - lam) * (s - R) ≤ 0 := by
        have h1 : lam * R / (mu - lam) ≤ s - R := by linarith [hs']
        rw [div_le_iff₀ hpos] at h1
        have h2 : (s - R) * (mu - lam) = (mu - lam) * (s - R) := by ring
        rw [h2] at h1
        linarith
      rw [max_eq_left hX]
  rw [heq.deriv_eq]
  exact deriv_const t 0

end FluidDynamics.Traffic.SignalQueue
