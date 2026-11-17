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
  rw [ite_eq_left hR]
  ring

/-- The queue is empty at the cycle end, under
`lam * (R + G) < mu * G` with `0 < lam < mu`. (Clearance inside the
green phase is `queueLen_eq_zero_of_clearance`.) -/
theorem queueLen_cycle_end {lam mu R G : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hcap : lam * (R + G) < mu * G) :
    queueLen lam mu R (R + G) = 0 := by
  unfold queueLen
  have _ := hmu
  by_cases hle : R + G ≤ R
  · exfalso
    have hG0 : G = 0 := by linarith
    subst hG0
    have hnonneg : 0 ≤ lam * R := mul_nonneg (le_of_lt hlam) hR
    simp at hcap
    linarith
  · rw [ite_eq_right hle]
    have hcap' : lam * R - (mu - lam) * G ≤ 0 := by linarith
    rw [show R + G - R = G by ring]
    exact max_eq_left hcap'

/-- Clearance offset: the queue is zero from time
`R + lam * R / (mu - lam)` onward. -/
theorem queueLen_eq_zero_of_clearance {lam mu R : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) {t : ℝ}
    (ht : R + lam * R / (mu - lam) ≤ t) :
    queueLen lam mu R t = 0 := by
  unfold queueLen
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have hXnonneg : 0 ≤ lam * R / (mu - lam) :=
    div_nonneg (mul_nonneg (le_of_lt hlam) hR) (le_of_lt hpos)
  by_cases hle : t ≤ R
  · rw [ite_eq_left hle]
    have hRt : R ≤ t := by linarith
    have htR : t = R := le_antisymm hle hRt
    have hX0 : lam * R / (mu - lam) = 0 := by linarith
    have hne : mu - lam ≠ 0 := ne_of_gt hpos
    have hlamR0 : lam * R = 0 := by
      have h := div_mul_cancel₀ (lam * R) hne
      rw [hX0, zero_mul] at h
      exact h.symm
    rw [htR, hlamR0]
  · rw [ite_eq_right hle]
    have hle2 : lam * R / (mu - lam) ≤ t - R := by linarith
    have hmul := mul_le_mul_of_nonneg_right hle2 (le_of_lt hpos)
    rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
    have hinner : lam * R - (mu - lam) * (t - R) ≤ 0 := by
      have hcomm : (t - R) * (mu - lam) = (mu - lam) * (t - R) := mul_comm _ _
      linarith
    exact max_eq_left hinner

/-- Nonnegativity at every nonnegative time. -/
theorem queueLen_nonneg {lam mu R : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ queueLen lam mu R t := by
  unfold queueLen
  by_cases hle : t ≤ R
  · rw [ite_eq_left hle]
    exact mul_nonneg (le_of_lt hlam) ht0
  · rw [ite_eq_right hle]
    exact le_max_left _ _

/-- Continuity on the cycle interval `[0, R + G]`. -/
theorem queueLen_continuousOn {lam mu R G : ℝ} (hlam : 0 ≤ lam)
    (hR : 0 ≤ R) (hG : 0 ≤ G) :
    ContinuousOn (queueLen lam mu R) (Set.Icc 0 (R + G)) := by
  have hlamR : 0 ≤ lam * R := mul_nonneg hlam hR
  have _ := hG
  have hf : Continuous (fun t : ℝ => lam * t) := by continuity
  have hinner : Continuous (fun t : ℝ => lam * R - (mu - lam) * (t - R)) := by
    continuity
  have hg : Continuous (fun t : ℝ => max 0 (lam * R - (mu - lam) * (t - R))) :=
    continuous_const.max hinner
  have hfid : Continuous (fun t : ℝ => t) := by continuity
  have hgconst : Continuous (fun _ : ℝ => R) := by continuity
  have heq : ∀ x : ℝ, (fun t : ℝ => t) x = (fun _ : ℝ => R) x →
      (fun t : ℝ => lam * t) x =
        (fun t : ℝ => max 0 (lam * R - (mu - lam) * (t - R))) x := by
    intro x hx
    have hx' : x = R := hx
    rw [hx']
    show lam * R = max 0 (lam * R - (mu - lam) * (R - R))
    rw [sub_self, mul_zero, sub_zero]
    exact (max_eq_right hlamR).symm
  have hcont : Continuous (queueLen lam mu R) := by
    unfold queueLen
    exact Continuous.if_le hf hg hfid hgconst heq
  exact hcont.continuousOn

/-- Red-phase rate: inside the red phase the queue derivative is
the arrival rate. -/
theorem queueLen_deriv_red {lam mu R t : ℝ} (ht : t < R) :
    deriv (queueLen lam mu R) t = lam := by
  have hmem : Set.Iio R ∈ nhds t := Iio_mem_nhds ht
  have heq : (fun s => queueLen lam mu R s) =ᶠ[nhds t] (fun s => lam * s) := by
    filter_upwards [hmem] with s hs
    unfold queueLen
    rw [ite_eq_left (le_of_lt hs)]
  calc deriv (queueLen lam mu R) t = deriv (fun s : ℝ => lam * s) t := heq.deriv_eq
    _ = lam := by
      have hdiff : DifferentiableAt ℝ (fun s : ℝ => s) t := by fun_prop
      rw [deriv_const_mul lam hdiff]
      have h1 : deriv (fun s : ℝ => s) t = 1 := congrFun deriv_id'' t
      rw [h1, mul_one]

/-- Green-phase rate before clearance: the derivative is
`-(mu - lam)`. -/
theorem queueLen_deriv_green {lam mu R t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (htR : R < t)
    (htc : t < R + lam * R / (mu - lam)) :
    deriv (queueLen lam mu R) t = -(mu - lam) := by
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have _ := hlam
  have hmem : Set.Ioo R (R + lam * R / (mu - lam)) ∈ nhds t :=
    Ioo_mem_nhds htR htc
  have heq : (fun s => queueLen lam mu R s) =ᶠ[nhds t]
      (fun s => lam * R - (mu - lam) * (s - R)) := by
    filter_upwards [hmem] with s hs
    unfold queueLen
    have hsR : R < s := hs.1
    have hsc : s < R + lam * R / (mu - lam) := hs.2
    rw [ite_eq_right (not_le_of_gt hsR)]
    have hinner_pos : 0 < lam * R - (mu - lam) * (s - R) := by
      have hle : s - R < lam * R / (mu - lam) := by linarith
      have hmul : (s - R) * (mu - lam) < lam * R / (mu - lam) * (mu - lam) :=
        mul_lt_mul_of_pos_right hle hpos
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
      have hcomm : (s - R) * (mu - lam) = (mu - lam) * (s - R) := mul_comm _ _
      rw [hcomm] at hmul
      linarith
    rw [max_eq_right (le_of_lt hinner_pos)]
  calc deriv (queueLen lam mu R) t
      = deriv (fun s : ℝ => lam * R - (mu - lam) * (s - R)) t := heq.deriv_eq
    _ = -(mu - lam) := by
      have hdiff1 : DifferentiableAt ℝ (fun s : ℝ => s - R) t := by fun_prop
      have hdiff2 : DifferentiableAt ℝ (fun s : ℝ => (mu - lam) * (s - R)) t :=
        hdiff1.const_mul _
      have hdiff3 : DifferentiableAt ℝ (fun _ : ℝ => lam * R) t := by fun_prop
      have hfun : (fun s : ℝ => lam * R - (mu - lam) * (s - R))
          = (fun _ : ℝ => lam * R) - (fun s : ℝ => (mu - lam) * (s - R)) := rfl
      rw [hfun, deriv_sub hdiff3 hdiff2, deriv_const]
      have hcm : deriv (fun s : ℝ => (mu - lam) * (s - R)) t
          = (mu - lam) * deriv (fun s : ℝ => s - R) t :=
        deriv_const_mul _ hdiff1
      rw [hcm]
      have hsr : deriv (fun s : ℝ => s - R) t = 1 := by
        rw [deriv_sub_const R]
        exact congrFun deriv_id'' t
      rw [hsr]
      ring

/-- After clearance the queue stays at zero: derivative `0`. -/
theorem queueLen_deriv_after_clearance {lam mu R t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R)
    (ht : R + lam * R / (mu - lam) < t) :
    deriv (queueLen lam mu R) t = 0 := by
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have hXnonneg : 0 ≤ lam * R / (mu - lam) :=
    div_nonneg (mul_nonneg (le_of_lt hlam) hR) (le_of_lt hpos)
  have hRt : R ≤ R + lam * R / (mu - lam) := by linarith
  have hmem : Set.Ioi (R + lam * R / (mu - lam)) ∈ nhds t := Ioi_mem_nhds ht
  have heq : (fun s => queueLen lam mu R s) =ᶠ[nhds t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hmem] with s hs
    unfold queueLen
    have hs_tc : R + lam * R / (mu - lam) < s := hs
    have hsR : R < s := lt_of_le_of_lt hRt hs_tc
    rw [ite_eq_right (not_le_of_gt hsR)]
    have hinner : lam * R - (mu - lam) * (s - R) ≤ 0 := by
      have hle : lam * R / (mu - lam) ≤ s - R := by linarith
      have hmul := mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
      rw [div_mul_cancel₀ _ (ne_of_gt hpos)] at hmul
      have hcomm : (s - R) * (mu - lam) = (mu - lam) * (s - R) := mul_comm _ _
      rw [hcomm] at hmul
      linarith
    rw [max_eq_left hinner]
  calc deriv (queueLen lam mu R) t = deriv (fun _ : ℝ => (0 : ℝ)) t := heq.deriv_eq
    _ = 0 := deriv_const _ _

end FluidDynamics.Traffic.SignalQueue
