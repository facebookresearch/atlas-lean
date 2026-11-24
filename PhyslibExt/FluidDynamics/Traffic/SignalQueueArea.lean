/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.FluidDynamics.Traffic.SignalQueue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# One-cycle queue area

## i. Overview

For the deterministic signal queue (`SignalQueue.queueLen`), the
area under the queue-length curve over one full cycle `[0, R + G]`
is `lam * R ^ 2 * mu / (2 * (mu - lam))`: the red-phase triangle
plus the green clearance triangle, under the cycle-capacity
condition that the queue clears within the cycle.

## ii. Key results

- `FluidDynamics.Traffic.SignalQueue.queueLen_integral_cycle`:
  the one-cycle queue area.

## iii. Table of contents

- A. The one-cycle area formula

## iv. References

- Standard deterministic queueing at fixed-time signals (fluid
  model), e.g. D. Gazis (ed.), *Traffic Science*, 1974.
-/

@[expose] public section

namespace FluidDynamics.Traffic.SignalQueue

/-! ## A. The one-cycle area formula -/

/-- Area under the queue-length curve over one cycle. -/
theorem queueLen_integral_cycle {lam mu R G : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hcap : lam * (R + G) ≤ mu * G) :
    ∫ t in (0)..(R + G), queueLen lam mu R t
      = lam * R ^ 2 * mu / (2 * (mu - lam)) := by
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have hpos' : mu - lam ≠ 0 := ne_of_gt hpos
  set c : ℝ := R + lam * R / (mu - lam) with hc
  have hlamR : 0 ≤ lam * R := mul_nonneg (le_of_lt hlam) hR
  have hw_nonneg : 0 ≤ lam * R / (mu - lam) := div_nonneg hlamR (le_of_lt hpos)
  have hRc : R ≤ c := by
    rw [hc]
    linarith [hw_nonneg]
  have hcap2 : lam * R ≤ (mu - lam) * G := by
    have h := hcap
    rw [mul_add] at h
    linarith [h]
  have hw_le : lam * R / (mu - lam) ≤ G := by
    rw [div_le_iff₀ hpos]
    linarith [hcap2]
  have hcG : c ≤ R + G := by
    rw [hc]
    linarith [hw_le]
  have h0c : 0 ≤ c := le_trans hR hRc
  have hRRG : R ≤ R + G := by linarith [hG]
  have hcont : ContinuousOn (queueLen lam mu R) (Set.Icc 0 (R + G)) :=
    queueLen_continuousOn (le_of_lt hlam) hR hG
  have hint0R : IntervalIntegrable (queueLen lam mu R) MeasureTheory.volume 0 R :=
    ContinuousOn.intervalIntegrable_of_Icc hR
      (hcont.mono (Set.Icc_subset_Icc_right hRRG))
  have hintRc : IntervalIntegrable (queueLen lam mu R) MeasureTheory.volume R c :=
    ContinuousOn.intervalIntegrable_of_Icc hRc
      (hcont.mono (Set.Icc_subset_Icc hR hcG))
  have hintcG :
      IntervalIntegrable (queueLen lam mu R) MeasureTheory.volume c (R + G) :=
    ContinuousOn.intervalIntegrable_of_Icc hcG
      (hcont.mono (Set.Icc_subset_Icc h0c le_rfl))
  have hsplit1 :=
    intervalIntegral.integral_add_adjacent_intervals hint0R (hintRc.trans hintcG)
  have hsplit2 := intervalIntegral.integral_add_adjacent_intervals hintRc hintcG
  have hP1 : (∫ t in (0)..R, queueLen lam mu R t) = lam * R ^ 2 / 2 := by
    have hcongr : (∫ t in (0)..R, queueLen lam mu R t) = ∫ t in (0)..R, lam * t := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      rw [Set.uIoo_of_le hR, Set.mem_Ioo] at hx
      have hxR : x ≤ R := le_of_lt hx.2
      simp [queueLen, hxR]
    rw [hcongr, intervalIntegral.integral_const_mul, integral_id]
    ring
  have hP3 : (∫ t in c..(R + G), queueLen lam mu R t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro x hx
    rw [Set.uIoc_of_le hcG, Set.mem_Ioc] at hx
    exact queueLen_eq_zero_of_clearance hlam hmu hR (le_of_lt hx.1)
  have hP2 : (∫ t in R..c, queueLen lam mu R t)
      = (c - R) * (lam * R) - (mu - lam) * (c - R) ^ 2 / 2 := by
    have hcongr : (∫ t in R..c, queueLen lam mu R t)
        = ∫ t in R..c, (lam * R - (mu - lam) * (t - R)) := by
      apply intervalIntegral.integral_congr_uIoo
      intro x hx
      rw [Set.uIoo_of_le hRc, Set.mem_Ioo] at hx
      have hxR : R < x := hx.1
      have hxc : x < c := hx.2
      have h1 : x - R < lam * R / (mu - lam) := by
        have hx_lt : x < R + lam * R / (mu - lam) := hxc
        linarith [hx_lt]
      have h4 : (mu - lam) * (x - R) < lam * R := by
        have h1' := (lt_div_iff₀ hpos).mp h1
        rwa [mul_comm (x - R) (mu - lam)] at h1'
      have hX : 0 ≤ lam * R - (mu - lam) * (x - R) := by linarith [h4]
      simp [queueLen, not_le_of_gt hxR, max_eq_right hX]
    rw [hcongr]
    have hintA : IntervalIntegrable (fun _ : ℝ => lam * R) MeasureTheory.volume R c :=
      intervalIntegrable_const
    have hintB :
        IntervalIntegrable (fun x : ℝ => (mu - lam) * (x - R)) MeasureTheory.volume R c :=
      ContinuousOn.intervalIntegrable_of_Icc hRc
        (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
    have hsub := intervalIntegral.integral_sub (a := R) (b := c) hintA hintB
    simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
      smul_eq_mul] at hsub
    have hshift : (∫ t in R..c, (t - R)) = ∫ t in (0)..(c - R), t := by
      have h := intervalIntegral.integral_comp_sub_right (fun x : ℝ => x) R (a := R) (b := c)
      simpa only [sub_self] using h
    rw [hsub, hshift, integral_id]
    ring
  have hcR : c - R = lam * R / (mu - lam) := by
    rw [hc]
    ring
  rw [← hsplit1, ← hsplit2, hP1, hP2, hP3, hcR]
  have h2m : 2 * (mu - lam) ≠ 0 := mul_ne_zero two_ne_zero hpos'
  field_simp
  ring

end FluidDynamics.Traffic.SignalQueue
