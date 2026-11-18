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
`lam`, service rate `mu`, red duration `R` (green duration `G` and
cycle `C = R + G` are theorem data, not parameters of this
function). Queue grows at rate `lam` during red and drains at rate
`mu - lam`
during green until it clears; clearance holds for admissible 0 < lam, lam < mu, 0 ≤ R (and by the cycle end under the capacity condition). -/
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
  unfold queueLen
  by_cases h : R + G ≤ R
  · rw [ite_eq_left h]
    have hmu0 : 0 < mu := lt_trans hlam hmu
    have hGle : G ≤ 0 := by linarith
    have h1 : mu * G ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmu0.le hGle
    have h2 : lam * (R + G) ≤ 0 := le_trans hcap h1
    have h3 : 0 ≤ lam * (R + G) := mul_nonneg hlam.le (by linarith)
    exact le_antisymm h2 h3
  · rw [ite_eq_right h]
    have hring : R + G - R = G := by ring
    rw [hring]
    apply max_eq_left
    linarith [hcap]

/-- Clearance offset: the queue is zero from time
`R + lam * R / (mu - lam)` onward. -/
theorem queueLen_eq_zero_of_clearance {lam mu R : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) {t : ℝ}
    (ht : R + lam * R / (mu - lam) ≤ t) :
    queueLen lam mu R t = 0 := by
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  unfold queueLen
  by_cases h : t ≤ R
  · rw [ite_eq_left h]
    have hX0 : 0 ≤ lam * R / (mu - lam) :=
      div_nonneg (mul_nonneg hlam.le hR) hpos.le
    have hXle : lam * R / (mu - lam) ≤ 0 := by linarith
    have hX : lam * R / (mu - lam) = 0 := le_antisymm hXle hX0
    have hlamR : lam * R = 0 := by
      rcases div_eq_zero_iff.mp hX with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hpos)
    have hR0 : R = 0 := by
      have hne : lam ≠ 0 := ne_of_gt hlam
      exact (mul_eq_zero.mp hlamR).resolve_left hne
    subst hR0
    rw [hX] at ht
    have ht0 : t = 0 := le_antisymm h (by linarith [ht])
    rw [ht0, mul_zero]
  · rw [ite_eq_right h]
    have h1 : lam * R / (mu - lam) ≤ t - R := by linarith [ht]
    have h2 : lam * R ≤ (mu - lam) * (t - R) := by
      have h3 := (div_le_iff₀ hpos).mp h1
      linarith [h3]
    apply max_eq_left
    linarith [h2]

/-- Nonnegativity at every nonnegative time. -/
theorem queueLen_nonneg {lam mu R : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ queueLen lam mu R t := by
  unfold queueLen
  by_cases h : t ≤ R
  · rw [ite_eq_left h]
    exact mul_nonneg hlam.le ht0
  · rw [ite_eq_right h]
    exact le_max_left 0 _

/-- Continuity on the cycle interval `[0, R + G]`. -/
theorem queueLen_continuousOn {lam mu R G : ℝ} (hlam : 0 ≤ lam)
    (hR : 0 ≤ R) (hG : 0 ≤ G) :
    ContinuousOn (queueLen lam mu R) (Set.Icc 0 (R + G)) := by
  have _hG : 0 ≤ G := hG
  have hQR : queueLen lam mu R R = lam * R := by
    unfold queueLen
    rw [ite_eq_left le_rfl]
  have hval : (fun s : ℝ => max 0 (lam * R - (mu - lam) * (s - R))) R = lam * R := by
    show max 0 (lam * R - (mu - lam) * (R - R)) = lam * R
    rw [sub_self, mul_zero, sub_zero, max_eq_right (mul_nonneg hlam hR)]
  have hlinC : Continuous (fun s : ℝ => lam * s) := continuous_id.const_mul lam
  have hsub2 : Continuous (fun s : ℝ => s - R) :=
    continuous_id.sub continuous_const
  have hmul : Continuous (fun s : ℝ => (mu - lam) * (s - R)) :=
    continuous_const.mul hsub2
  have hsub : Continuous (fun s : ℝ => lam * R - (mu - lam) * (s - R)) :=
    continuous_const.sub hmul
  have hmaxC : Continuous (fun s : ℝ => max 0 (lam * R - (mu - lam) * (s - R))) :=
    continuous_const.max hsub
  have hcontR : ContinuousAt (queueLen lam mu R) R := by
    have hleft : ContinuousAt (fun s : ℝ => lam * s) R := hlinC.continuousAt
    have hright : ContinuousAt (fun s : ℝ => max 0 (lam * R - (mu - lam) * (s - R))) R :=
      hmaxC.continuousAt
    rw [Metric.continuousAt_iff] at hleft hright ⊢
    intro ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := hleft ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := hright ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs => ?_⟩
    have hs1 : dist s R < δ₁ := lt_of_lt_of_le hs (min_le_left _ _)
    have hs2 : dist s R < δ₂ := lt_of_lt_of_le hs (min_le_right _ _)
    by_cases h : s ≤ R
    · have hqs : queueLen lam mu R s = lam * s := by
        unfold queueLen
        rw [ite_eq_left h]
      rw [hqs, hQR]
      exact h₁ hs1
    · have hqs : queueLen lam mu R s = max 0 (lam * R - (mu - lam) * (s - R)) := by
        unfold queueLen
        rw [ite_eq_right h]
      have hval' : max 0 (lam * R - (mu - lam) * (R - R)) = lam * R := hval
      have h₂' := h₂ hs2
      rw [hqs, hQR]
      rw [hval'] at h₂'
      exact h₂'
  have hcont : Continuous (queueLen lam mu R) := by
    rw [continuous_iff_continuousAt]
    intro x
    rcases lt_trichotomy x R with hxr | hxr | hxr
    · have hform : ContinuousAt (fun s : ℝ => lam * s) x := hlinC.continuousAt
      have heq : queueLen lam mu R =ᶠ[𝓝 x] (fun s : ℝ => lam * s) := by
        filter_upwards [Iio_mem_nhds hxr] with s hs
        have hsR : s < R := Set.mem_Iio.mp hs
        show queueLen lam mu R s = lam * s
        unfold queueLen
        rw [ite_eq_left hsR.le]
      exact hform.congr_of_eventuallyEq heq
    · subst hxr
      exact hcontR
    · have hform : ContinuousAt (fun s : ℝ => max 0 (lam * R - (mu - lam) * (s - R))) x :=
        hmaxC.continuousAt
      have heq : queueLen lam mu R =ᶠ[𝓝 x]
          (fun s : ℝ => max 0 (lam * R - (mu - lam) * (s - R))) := by
        filter_upwards [Ioi_mem_nhds hxr] with s hs
        have hsR : R < s := Set.mem_Ioi.mp hs
        show queueLen lam mu R s = max 0 (lam * R - (mu - lam) * (s - R))
        unfold queueLen
        rw [ite_eq_right (not_le.mpr hsR)]
      exact hform.congr_of_eventuallyEq heq
  exact hcont.continuousOn

/-- Red-phase rate: inside the red phase the queue derivative is
the arrival rate. -/
theorem queueLen_hasDerivAt_red {lam mu R t : ℝ} (ht0 : 0 ≤ t) (ht : t < R) :
    HasDerivAt (queueLen lam mu R) lam t := by
  have hbase : HasDerivAt (fun s : ℝ => lam * s) lam t := by
    simpa using (hasDerivAt_id' t).const_mul lam
  have hneg : (-1 : ℝ) < t := by linarith [ht0]
  have heq : queueLen lam mu R =ᶠ[𝓝 t] (fun s : ℝ => lam * s) := by
    filter_upwards [Ioo_mem_nhds hneg ht] with s hs
    have hsR : s < R := (Set.mem_Ioo.mp hs).2
    show queueLen lam mu R s = lam * s
    unfold queueLen
    rw [ite_eq_left hsR.le]
  exact hbase.congr_of_eventuallyEq heq

/-- Red-phase rate: inside the red phase the queue derivative is
the arrival rate. -/
theorem queueLen_deriv_red {lam mu R t : ℝ} (ht0 : 0 ≤ t) (ht : t < R) :
    deriv (queueLen lam mu R) t = lam := by
  exact (queueLen_hasDerivAt_red ht0 ht).deriv

/-- Green-phase rate before clearance: the derivative is
`-(mu - lam)`. -/
theorem queueLen_hasDerivAt_green {lam mu R G t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (htR : R < t)
    (htc : t < R + lam * R / (mu - lam)) (htG : t < R + G) :
    HasDerivAt (queueLen lam mu R) (-(mu - lam)) t := by
  have _hlam : 0 < lam := hlam
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have h1 : HasDerivAt (fun s : ℝ => s - R) 1 t := (hasDerivAt_id' t).sub_const R
  have h2 : HasDerivAt (fun s : ℝ => (mu - lam) * (s - R)) ((mu - lam) * 1) t :=
    h1.const_mul (mu - lam)
  have hbase : HasDerivAt (fun s : ℝ => lam * R - (mu - lam) * (s - R)) (-(mu - lam)) t := by
    have h4 := h2.const_sub (lam * R)
    rw [mul_one] at h4
    exact h4
  have heq : queueLen lam mu R =ᶠ[𝓝 t]
      (fun s : ℝ => lam * R - (mu - lam) * (s - R)) := by
    filter_upwards [Ioo_mem_nhds htR (lt_min htc htG)] with s hs
    obtain ⟨hsR, hsmin⟩ := Set.mem_Ioo.mp hs
    have hsc : s < R + lam * R / (mu - lam) := lt_of_lt_of_le hsmin (min_le_left _ _)
    have hlt : s - R < lam * R / (mu - lam) := by linarith
    have hmul : (s - R) * (mu - lam) < lam * R := (lt_div_iff₀ hpos).mp hlt
    have harg : 0 < lam * R - (mu - lam) * (s - R) := by linarith
    show queueLen lam mu R s = lam * R - (mu - lam) * (s - R)
    unfold queueLen
    rw [ite_eq_right (not_le.mpr hsR), max_eq_right harg.le]
  exact hbase.congr_of_eventuallyEq heq

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
  have hbase : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
  have hGt : t < R + G + 1 := by linarith [htG]
  have heq : queueLen lam mu R =ᶠ[𝓝 t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [Ioo_mem_nhds ht hGt] with s hs
    have hsC : R + lam * R / (mu - lam) < s := (Set.mem_Ioo.mp hs).1
    have h0 : queueLen lam mu R s = 0 :=
      queueLen_eq_zero_of_clearance hlam hmu hR hsC.le
    show queueLen lam mu R s = 0
    exact h0
  exact hbase.congr_of_eventuallyEq heq

/-- After clearance the queue stays at zero: derivative `0`. -/
theorem queueLen_deriv_after_clearance {lam mu R G t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) (htG : t ≤ R + G)
    (ht : R + lam * R / (mu - lam) < t) :
    deriv (queueLen lam mu R) t = 0 := by
  exact (queueLen_hasDerivAt_after_clearance hlam hmu hR htG ht).deriv

end FluidDynamics.Traffic.SignalQueue
