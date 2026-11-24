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

open scoped Topology

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
`lam`, service rate `mu`, red duration `R`. During red (`t ≤ R`)
the queue grows at rate `lam`; after red it drains at rate
`mu - lam` until it clears and then stays at zero. That draining
description is the physical regime `0 < lam < mu` with `0 ≤ R`,
which the results below assume; for general real parameters the
definition is the same totalized piecewise formula. Green
duration and cycle length are not parameters of `queueLen`: they
enter only through `queueLen_cycle_end`, where the green duration
is supplied explicitly. -/
noncomputable def queueLen (lam mu R : ℝ) (t : ℝ) : ℝ :=
  if t ≤ R then lam * t
  else max 0 (lam * R - (mu - lam) * (t - R))

/-- The queue starts empty. -/
theorem queueLen_zero {lam mu R : ℝ} (hR : 0 ≤ R) :
    queueLen lam mu R 0 = 0 := by
  simp [queueLen, hR]

/-- The queue is empty at the cycle end, under
`lam * (R + G) ≤ mu * G` with `0 < lam < mu`. -/
theorem queueLen_cycle_end {lam mu R G : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hcap : lam * (R + G) ≤ mu * G) :
    queueLen lam mu R (R + G) = 0 := by
  have _hpos : 0 < mu - lam := sub_pos.mpr hmu
  unfold queueLen
  split_ifs with h
  · have hG0 : G = 0 := le_antisymm (by linarith) hG
    subst hG0
    simp only [add_zero, mul_zero] at hcap ⊢
    exact le_antisymm hcap (mul_nonneg (le_of_lt hlam) hR)
  · have _ : ¬ (R + G ≤ R) := h
    have hcap2 : lam * R + lam * G ≤ mu * G := by
      have hcap' := hcap
      rwa [mul_add] at hcap'
    have hX : lam * R - (mu - lam) * (R + G - R) ≤ 0 := by
      have hRG : R + G - R = G := by ring
      rw [hRG, sub_mul]
      linarith
    exact max_eq_left hX

/-- Clearance offset: the queue is zero from time
`R + lam * R / (mu - lam)` onward. -/
theorem queueLen_eq_zero_of_clearance {lam mu R : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) {t : ℝ}
    (ht : R + lam * R / (mu - lam) ≤ t) :
    queueLen lam mu R t = 0 := by
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have hnn : 0 ≤ lam * R / (mu - lam) :=
    div_nonneg (mul_nonneg (le_of_lt hlam) hR) (le_of_lt hpos)
  have hRt : R ≤ t := by linarith
  unfold queueLen
  split_ifs with h
  · have htR : t = R := le_antisymm h hRt
    have hle : lam * R / (mu - lam) ≤ 0 := by linarith
    have hle2 : lam * R ≤ 0 := by
      have h3 := (div_le_iff₀ hpos).mp hle
      rwa [zero_mul] at h3
    have hlamR : lam * R = 0 :=
      le_antisymm hle2 (mul_nonneg (le_of_lt hlam) hR)
    rw [htR]
    exact hlamR
  · have _ : ¬ (t ≤ R) := h
    have h1 : lam * R / (mu - lam) ≤ t - R := by linarith
    have h4 : lam * R ≤ (mu - lam) * (t - R) :=
      calc lam * R ≤ (t - R) * (mu - lam) := (div_le_iff₀ hpos).mp h1
        _ = (mu - lam) * (t - R) := mul_comm _ _
    have hX : lam * R - (mu - lam) * (t - R) ≤ 0 := by linarith
    exact max_eq_left hX

/-- Nonnegativity at every nonnegative time. -/
theorem queueLen_nonneg {lam mu R : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ queueLen lam mu R t := by
  by_cases h : t ≤ R
  · have heq : queueLen lam mu R t = lam * t := by simp [queueLen, h]
    rw [heq]
    exact mul_nonneg (le_of_lt hlam) ht0
  · have heq : queueLen lam mu R t = max 0 (lam * R - (mu - lam) * (t - R)) := by
      simp [queueLen, h]
    rw [heq]
    exact le_max_left _ _

/-- Continuity on the cycle interval `[0, R + G]`. -/
theorem queueLen_continuousOn {lam mu R G : ℝ} (hlam : 0 ≤ lam)
    (hR : 0 ≤ R) (hG : 0 ≤ G) :
    ContinuousOn (queueLen lam mu R) (Set.Icc 0 (R + G)) := by
  have _ : 0 ≤ G := hG
  have hcont : Continuous (queueLen lam mu R) := by
    show Continuous fun t : ℝ =>
      if t ≤ R then lam * t else max 0 (lam * R - (mu - lam) * (t - R))
    refine Continuous.if ?agree ?hf ?hg
    · intro a ha
      have hfront : frontier {x : ℝ | x ≤ R} = {R} := frontier_Iic
      rw [hfront, Set.mem_singleton_iff] at ha
      subst ha
      simp only [sub_self, mul_zero, sub_zero]
      exact (max_eq_right (mul_nonneg hlam hR)).symm
    · exact continuous_const.mul continuous_id
    · exact continuous_const.max
        (continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const)))
  exact hcont.continuousOn

/-- Red-phase rate: inside the red phase the queue derivative is
the arrival rate. -/
theorem queueLen_hasDerivAt_red {lam mu R t : ℝ} (ht0 : 0 < t) (ht : t < R) :
    HasDerivAt (queueLen lam mu R) lam t := by
  have _ : 0 < t := ht0
  have hbase : HasDerivAt (fun t' : ℝ => lam * t') lam t := by
    have h := HasDerivAt.const_mul lam (hasDerivAt_id t)
    rwa [mul_one] at h
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds ht] with t' ht'
  have ht'' : t' < R := ht'
  show queueLen lam mu R t' = lam * t'
  simp [queueLen, le_of_lt ht'']

/-- Red-phase rate: inside the red phase the queue derivative is
the arrival rate. -/
theorem queueLen_deriv_red {lam mu R t : ℝ} (ht0 : 0 < t) (ht : t < R) :
    deriv (queueLen lam mu R) t = lam := by
  exact (queueLen_hasDerivAt_red ht0 ht).deriv

/-- Green-phase rate before clearance: the derivative is
`-(mu - lam)`. -/
theorem queueLen_hasDerivAt_green {lam mu R G t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (htR : R < t)
    (htc : t < R + lam * R / (mu - lam)) (htG : t < R + G) :
    HasDerivAt (queueLen lam mu R) (-(mu - lam)) t := by
  have _ : 0 < lam := hlam
  have _ : t < R + G := htG
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have hmul : HasDerivAt (fun t' : ℝ => (mu - lam) * (t' - R)) ((mu - lam) * 1) t :=
    HasDerivAt.const_mul (mu - lam) (HasDerivAt.sub_const R (hasDerivAt_id t))
  have hbase : HasDerivAt (fun t' : ℝ => lam * R - (mu - lam) * (t' - R))
      (-(mu - lam)) t := by
    have h := HasDerivAt.const_sub (lam * R) hmul
    rwa [mul_one] at h
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds htR, Iio_mem_nhds htc] with t' htR' htc'
  have htR'' : R < t' := htR'
  have htc'' : t' < R + lam * R / (mu - lam) := htc'
  have h1 : t' - R < lam * R / (mu - lam) := by linarith
  have h4 : (mu - lam) * (t' - R) < lam * R :=
    calc (mu - lam) * (t' - R) = (t' - R) * (mu - lam) := mul_comm _ _
      _ < lam * R := (lt_div_iff₀ hpos).mp h1
  have hX : 0 < lam * R - (mu - lam) * (t' - R) := by linarith
  show queueLen lam mu R t' = lam * R - (mu - lam) * (t' - R)
  simp [queueLen, not_le_of_gt htR'', max_eq_right (le_of_lt hX)]

/-- Green-phase rate before clearance: the derivative is
`-(mu - lam)`. -/
theorem queueLen_deriv_green {lam mu R G t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (htR : R < t)
    (htc : t < R + lam * R / (mu - lam)) (htG : t < R + G) :
    deriv (queueLen lam mu R) t = -(mu - lam) := by
  exact (queueLen_hasDerivAt_green hlam hmu htR htc htG).deriv

/-- After clearance the queue stays at zero: derivative `0`. -/
theorem queueLen_hasDerivAt_after_clearance {lam mu R G t : ℝ}
    (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) (htG : t ≤ R + G)
    (ht : R + lam * R / (mu - lam) < t) :
    HasDerivAt (queueLen lam mu R) 0 t := by
  have _ : t ≤ R + G := htG
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have hnn : 0 ≤ lam * R / (mu - lam) :=
    div_nonneg (mul_nonneg (le_of_lt hlam) hR) (le_of_lt hpos)
  have hclear : R ≤ R + lam * R / (mu - lam) := by linarith
  have hbase := hasDerivAt_const t (0 : ℝ)
  refine hbase.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds ht] with t' ht'
  have hc'' : R + lam * R / (mu - lam) < t' := ht'
  have htR'' : R < t' := lt_of_le_of_lt hclear hc''
  have h1 : lam * R / (mu - lam) < t' - R := by linarith
  have h4 : lam * R < (mu - lam) * (t' - R) :=
    calc lam * R < (t' - R) * (mu - lam) := (div_lt_iff₀ hpos).mp h1
      _ = (mu - lam) * (t' - R) := mul_comm _ _
  have hX : lam * R - (mu - lam) * (t' - R) ≤ 0 := by linarith
  show queueLen lam mu R t' = 0
  simp [queueLen, not_le_of_gt htR'', max_eq_left hX]

/-- After clearance the queue stays at zero: derivative `0`. -/
theorem queueLen_deriv_after_clearance {lam mu R G t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) (htG : t ≤ R + G)
    (ht : R + lam * R / (mu - lam) < t) :
    deriv (queueLen lam mu R) t = 0 := by
  exact (queueLen_hasDerivAt_after_clearance hlam hmu hR htG ht).deriv

end FluidDynamics.Traffic.SignalQueue
