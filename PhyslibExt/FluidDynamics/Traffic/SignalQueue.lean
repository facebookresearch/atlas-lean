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
`lam * (R + G) < mu * G` with `0 < lam < mu`. (Clearance inside the
green phase is `queueLen_eq_zero_of_clearance`.) -/
theorem queueLen_cycle_end {lam mu R G : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) (hG : 0 ≤ G)
    (hcap : lam * (R + G) < mu * G) :
    queueLen lam mu R (R + G) = 0 := by
  unfold queueLen
  by_cases h : R + G ≤ R
  · rw [ite_eq_left h]
    have hG0 : G ≤ 0 := by linarith
    have h1 : 0 ≤ lam * (R + G) := mul_nonneg (le_of_lt hlam) (add_nonneg hR hG)
    have hmu0 : 0 ≤ mu := le_of_lt (lt_trans hlam hmu)
    have h2 : mu * G ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hmu0 hG0
    linarith
  · rw [ite_eq_right h]
    have hRG : (R + G : ℝ) - R = G := by ring
    rw [hRG]
    apply max_eq_left
    have hdist : lam * (R + G) = lam * R + lam * G := by ring
    have hmuG : mu * G = (mu - lam) * G + lam * G := by ring
    linarith

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
    have hc_nonneg : 0 ≤ lam * R / (mu - lam) :=
      div_nonneg (mul_nonneg (le_of_lt hlam) hR) (le_of_lt hpos)
    have hc_le : lam * R / (mu - lam) ≤ 0 := by linarith
    have hc0 : lam * R / (mu - lam) = 0 := le_antisymm hc_le hc_nonneg
    have hlamR : lam * R = 0 := by
      rcases (div_eq_zero_iff.mp hc0) with h' | h'
      · exact h'
      · exact absurd h' (ne_of_gt hpos)
    have htR : t = R := by linarith
    rw [htR]
    exact hlamR
  · rw [ite_eq_right h]
    have hle : lam * R / (mu - lam) ≤ t - R := by linarith
    have hmul : lam * R ≤ (t - R) * (mu - lam) := (div_le_iff₀ hpos).mp hle
    have hcomm : (mu - lam) * (t - R) = (t - R) * (mu - lam) := mul_comm _ _
    apply max_eq_left
    linarith

/-- Nonnegativity at every nonnegative time. -/
theorem queueLen_nonneg {lam mu R : ℝ} (hlam : 0 < lam)
    {t : ℝ} (ht0 : 0 ≤ t) :
    0 ≤ queueLen lam mu R t := by
  unfold queueLen
  by_cases h : t ≤ R
  · rw [ite_eq_left h]
    exact mul_nonneg (le_of_lt hlam) ht0
  · rw [ite_eq_right h]
    exact le_max_left _ _

/-- Continuity on the cycle interval `[0, R + G]`. -/
theorem queueLen_continuousOn {lam mu R G : ℝ} (hlam : 0 ≤ lam)
    (hR : 0 ≤ R) (hG : 0 ≤ G) :
    ContinuousOn (queueLen lam mu R) (Set.Icc 0 (R + G)) := by
  have _ := hG
  have hlamR : 0 ≤ lam * R := mul_nonneg hlam hR
  have hg2 : Continuous (fun t : ℝ => lam * R - (mu - lam) * (t - R)) :=
    continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))
  have hg : Continuous (fun t : ℝ => max 0 (lam * R - (mu - lam) * (t - R))) :=
    continuous_const.max hg2
  have hset : Set.Icc 0 (R + G) ∩ Set.Iic R ∪ (Set.Icc 0 (R + G) ∩ Set.Ici R)
      = Set.Icc 0 (R + G) := by
    ext t
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_Icc, Set.mem_Iic, Set.mem_Ici]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩)
      · exact h
      · exact h
    · intro h
      rcases le_total t R with hl | hr
      · exact Or.inl ⟨h, hl⟩
      · exact Or.inr ⟨h, hr⟩
  intro x hx
  rcases lt_trichotomy x R with hlt | heq | hgt
  · have hxval : queueLen lam mu R x = lam * x := by
      unfold queueLen
      rw [ite_eq_left (le_of_lt hlt)]
    have hev : (queueLen lam mu R) =ᶠ[nhds x] (fun t : ℝ => lam * t) := by
      filter_upwards [eventually_lt_nhds hlt] with t ht
      show queueLen lam mu R t = lam * t
      unfold queueLen
      rw [ite_eq_left (le_of_lt ht)]
    have hten : Filter.Tendsto (fun t : ℝ => lam * t) (nhds x) (nhds (lam * x)) :=
      continuousAt_const.mul continuousAt_id
    have hcon : ContinuousAt (queueLen lam mu R) x := by
      show Filter.Tendsto (queueLen lam mu R) (nhds x) (nhds (queueLen lam mu R x))
      rw [hxval]
      exact hten.congr' hev.symm
    exact hcon.continuousWithinAt
  · rw [heq] at hx ⊢
    rw [← hset]
    refine ContinuousWithinAt.union ?_ ?_
    · refine ContinuousWithinAt.congr (f := fun t : ℝ => lam * t) ?_ ?_ ?_
      · exact (continuous_id.const_mul lam).continuousWithinAt
      · intro y hy
        have hyR : y ≤ R := Set.mem_Iic.mp hy.2
        show queueLen lam mu R y = lam * y
        unfold queueLen
        rw [ite_eq_left hyR]
      · show queueLen lam mu R R = lam * R
        unfold queueLen
        rw [ite_eq_left le_rfl]
    · refine ContinuousWithinAt.congr
        (f := fun t : ℝ => max 0 (lam * R - (mu - lam) * (t - R))) ?_ ?_ ?_
      · exact hg.continuousWithinAt
      · intro y hy
        have hyR : R ≤ y := Set.mem_Ici.mp hy.2
        rcases eq_or_lt_of_le hyR with rfl | hlt
        · show queueLen lam mu R R = max 0 (lam * R - (mu - lam) * (R - R))
          unfold queueLen
          rw [ite_eq_left le_rfl, sub_self, mul_zero, sub_zero, max_eq_right hlamR]
        · show queueLen lam mu R y = max 0 (lam * R - (mu - lam) * (y - R))
          unfold queueLen
          rw [ite_eq_right (not_le.mpr hlt)]
      · show queueLen lam mu R R = max 0 (lam * R - (mu - lam) * (R - R))
        unfold queueLen
        rw [ite_eq_left le_rfl, sub_self, mul_zero, sub_zero, max_eq_right hlamR]
  · have hxval : queueLen lam mu R x
        = max 0 (lam * R - (mu - lam) * (x - R)) := by
      unfold queueLen
      rw [ite_eq_right (not_le.mpr hgt)]
    have hev : (queueLen lam mu R) =ᶠ[nhds x]
        (fun t : ℝ => max 0 (lam * R - (mu - lam) * (t - R))) := by
      filter_upwards [eventually_gt_nhds hgt] with t ht
      show queueLen lam mu R t = max 0 (lam * R - (mu - lam) * (t - R))
      unfold queueLen
      rw [ite_eq_right (not_le.mpr ht)]
    have hten : Filter.Tendsto (fun t : ℝ => max 0 (lam * R - (mu - lam) * (t - R)))
        (nhds x) (nhds (max 0 (lam * R - (mu - lam) * (x - R)))) :=
      hg.continuousAt
    have hcon : ContinuousAt (queueLen lam mu R) x := by
      show Filter.Tendsto (queueLen lam mu R) (nhds x) (nhds (queueLen lam mu R x))
      rw [hxval]
      exact hten.congr' hev.symm
    exact hcon.continuousWithinAt

/-- Red-phase rate: inside the red phase the queue derivative is
the arrival rate. -/
theorem queueLen_deriv_red {lam mu R t : ℝ} (ht : t < R) :
    deriv (queueLen lam mu R) t = lam := by
  have hev : (queueLen lam mu R) =ᶠ[nhds t] (fun t' : ℝ => lam * t') := by
    filter_upwards [eventually_lt_nhds ht] with t' ht'
    show queueLen lam mu R t' = lam * t'
    unfold queueLen
    rw [ite_eq_left (le_of_lt ht')]
  rw [hev.deriv_eq]
  rw [show (fun t' : ℝ => lam * t') = (fun t' => lam * id t') from rfl,
    deriv_const_mul _ differentiableAt_id, deriv_id, mul_one]

/-- Green-phase rate before clearance: the derivative is
`-(mu - lam)`. -/
theorem queueLen_deriv_green {lam mu R G t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (htR : R < t)
    (htc : t < R + lam * R / (mu - lam)) (htG : t < R + G) :
    deriv (queueLen lam mu R) t = -(mu - lam) := by
  have _ := hlam
  have _ := htG
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have h1 : t - R < lam * R / (mu - lam) := by linarith
  have h2 : (t - R) * (mu - lam) < lam * R := (lt_div_iff₀ hpos).mp h1
  have hcomm : (mu - lam) * (t - R) = (t - R) * (mu - lam) := mul_comm _ _
  have hv : 0 < lam * R - (mu - lam) * (t - R) := by linarith
  have hcontV : ContinuousAt (fun t' : ℝ => lam * R - (mu - lam) * (t' - R)) t :=
    continuousAt_const.sub
      (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
  have hevR : ∀ᶠ t' in nhds t, R < t' := eventually_gt_nhds htR
  have hevV : ∀ᶠ t' in nhds t, 0 < lam * R - (mu - lam) * (t' - R) :=
    Filter.Tendsto.eventually_const_lt hv hcontV
  have hev : (queueLen lam mu R) =ᶠ[nhds t]
      (fun t' : ℝ => lam * R - (mu - lam) * (t' - R)) := by
    filter_upwards [hevR, hevV] with t' htR' hv'
    show queueLen lam mu R t' = lam * R - (mu - lam) * (t' - R)
    unfold queueLen
    rw [ite_eq_right (not_le.mpr htR'), max_eq_right (le_of_lt hv')]
  rw [hev.deriv_eq]
  rw [show (fun t' : ℝ => lam * R - (mu - lam) * (t' - R))
      = (fun t' => lam * R - (mu - lam) * (id t' - R)) from rfl,
    deriv_const_sub, deriv_const_mul _ (differentiableAt_id.sub_const R),
    deriv_sub_const, deriv_id]
  ring

/-- After clearance the queue stays at zero: derivative `0`. -/
theorem queueLen_deriv_after_clearance {lam mu R G t : ℝ} (hlam : 0 < lam)
    (hmu : lam < mu) (hR : 0 ≤ R) (htG : t ≤ R + G)
    (ht : R + lam * R / (mu - lam) < t) :
    deriv (queueLen lam mu R) t = 0 := by
  have _ := htG
  have hpos : 0 < mu - lam := sub_pos.mpr hmu
  have hc_nonneg : 0 ≤ lam * R / (mu - lam) :=
    div_nonneg (mul_nonneg (le_of_lt hlam) hR) (le_of_lt hpos)
  have hRt : R < t := by linarith
  have h1 : lam * R / (mu - lam) < t - R := by linarith
  have h2 : lam * R < (t - R) * (mu - lam) := (div_lt_iff₀ hpos).mp h1
  have hcomm : (mu - lam) * (t - R) = (t - R) * (mu - lam) := mul_comm _ _
  have hv : lam * R - (mu - lam) * (t - R) < 0 := by linarith
  have hcontV : ContinuousAt (fun t' : ℝ => lam * R - (mu - lam) * (t' - R)) t :=
    continuousAt_const.sub
      (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
  have hevR : ∀ᶠ t' in nhds t, R < t' := eventually_gt_nhds hRt
  have hevV : ∀ᶠ t' in nhds t, lam * R - (mu - lam) * (t' - R) < 0 :=
    Filter.Tendsto.eventually_lt_const hv hcontV
  have hev : (queueLen lam mu R) =ᶠ[nhds t] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [hevR, hevV] with t' htR' hv'
    show queueLen lam mu R t' = 0
    unfold queueLen
    rw [ite_eq_right (not_le.mpr htR'), max_eq_left (le_of_lt hv')]
  rw [hev.deriv_eq]
  exact deriv_const t 0

end FluidDynamics.Traffic.SignalQueue
