/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Water-hammer energy flux

## i. Overview

For the first-order water-hammer system on `[0, L]`, the total
energy `E(t) = ∫_0^L [(gA/a²) h²/2 + q²/(2gA)] dx` satisfies
`E'(t) = h(t,0) q(t,0) - h(t,L) q(t,L)`: energy changes only through
the boundary flux (physical energy is `rho * g * E`).

## ii. Key results

- `WaterHammerEnergy.energy_hasDerivAt`: the flux identity.

## iii. Table of contents

- A. Energy flux

## iv. References

- E. B. Wylie and V. L. Streeter, *Fluid Transients in Systems*,
  Prentice Hall, 1993 (water-hammer energy balance).

## A. Energy flux
-/

@[expose] public section

namespace WaterHammerEnergy

open MeasureTheory intervalIntegral

/-- Energy flux identity for the water-hammer system on `[0, L]`:
with energy density `e t x = (gA/a²) h²/2 + q²/(2 gA)` built from
state functions `h q` whose supplied partial derivatives `ht hx qt qx`
satisfy `ht + (a²/(gA)) qx = 0` and `qt + gA hx = 0` on the interval,
the total energy `E t = ∫ x in 0..L, e t x` has derivative
`h t 0 * q t 0 - h t L * q t L` (times the physical factor `rho * g`
for physical energy, not part of this identity). -/
theorem energy_hasDerivAt {a g A L : ℝ} (ha : 0 < a) (hg : 0 < g)
    (hA : 0 < A) (hL : 0 < L)
    (h q ht hx qt qx : ℝ → ℝ → ℝ)
    (hht : ∀ t x : ℝ, x ∈ Set.Icc 0 L → HasDerivAt (fun s => h s x) (ht t x) t)
    (hqt : ∀ t x : ℝ, x ∈ Set.Icc 0 L → HasDerivAt (fun s => q s x) (qt t x) t)
    (hhx : ∀ t x : ℝ, x ∈ Set.Icc 0 L → HasDerivAt (h t) (hx t x) x)
    (hqx : ∀ t x : ℝ, x ∈ Set.Icc 0 L → HasDerivAt (q t) (qx t x) x)
    (hpde1 : ∀ t x : ℝ, x ∈ Set.Icc 0 L → ht t x + (a^2 / (g * A)) * qx t x = 0)
    (hpde2 : ∀ t x : ℝ, x ∈ Set.Icc 0 L → qt t x + (g * A) * hx t x = 0)
    (hhtcont : ContinuousOn (fun p : ℝ × ℝ => ht p.1 p.2)
      (Set.univ ×ˢ Set.Icc 0 L))
    (hqtcont : ContinuousOn (fun p : ℝ × ℝ => qt p.1 p.2)
      (Set.univ ×ˢ Set.Icc 0 L))
    (t : ℝ) :
    HasDerivAt (fun s => ∫ x in (0:ℝ)..L,
        (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
      (h t 0 * q t 0 - h t L * q t L) t := by
  have h0L : (0:ℝ) ≤ L := hL.le
  have hgA : (0:ℝ) < g * A := mul_pos hg hA
  have hgA' : g * A ≠ 0 := ne_of_gt hgA
  have ha2 : (0:ℝ) < a ^ 2 := pow_pos ha 2
  have ha2' : a ^ 2 ≠ 0 := ne_of_gt ha2
  have hc1 : (0:ℝ) < g * A / a ^ 2 := div_pos hgA ha2
  have h2gA' : (2:ℝ) * g * A ≠ 0 := ne_of_gt (mul_pos (mul_pos two_pos hg) hA)
  have hcont_h : ∀ s : ℝ, ContinuousOn (h s) (Set.Icc 0 L) :=
    fun s => HasDerivAt.continuousOn (fun x hx => hhx s x hx)
  have hcont_q : ∀ s : ℝ, ContinuousOn (q s) (Set.Icc 0 L) :=
    fun s => HasDerivAt.continuousOn (fun x hx => hqx s x hx)
  have hcont_ht : ∀ s : ℝ, ContinuousOn (fun x => ht s x) (Set.Icc 0 L) := by
    intro s
    exact hhtcont.comp' ((continuousOn_const (c := s)).prodMk continuousOn_id)
      (fun x hx => Set.mk_mem_prod trivial hx)
  have hcont_qt : ∀ s : ℝ, ContinuousOn (fun x => qt s x) (Set.Icc 0 L) := by
    intro s
    exact hqtcont.comp' ((continuousOn_const (c := s)).prodMk continuousOn_id)
      (fun x hx => Set.mk_mem_prod trivial hx)
  have hcont_E : ∀ s : ℝ, ContinuousOn
      (fun x => (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
      (Set.Icc 0 L) := by
    intro s
    have hh := hcont_h s
    have hq := hcont_q s
    fun_prop
  have hsub : Set.uIoc 0 L ⊆ Set.Icc 0 L := by
    rw [Set.uIoc_of_le h0L]
    exact Set.Ioc_subset_Icc_self
  have hFint : IntervalIntegrable
      (fun x => (g * A / a^2) * (h t x)^2 / 2 + (q t x)^2 / (2 * g * A))
      volume 0 L :=
    (hcont_E t).intervalIntegrable_of_Icc h0L
  have hFmeas : Filter.Eventually
      (fun s => AEStronglyMeasurable
        (fun x => (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
        (volume.restrict (Set.uIoc 0 L))) (nhds t) :=
    Filter.Eventually.of_forall fun s =>
      ((hcont_E s).mono hsub).aestronglyMeasurable measurableSet_uIoc
  have hKc : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc 0 L) :=
    isCompact_Icc.prod isCompact_Icc
  have hsubK : Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc 0 L
      ⊆ Set.univ ×ˢ Set.Icc 0 L :=
    fun p hp => Set.mk_mem_prod (Set.mem_univ _) hp.2
  obtain ⟨Cht, hCht⟩ := hKc.exists_bound_of_continuousOn (hhtcont.mono hsubK)
  obtain ⟨Cqt, hCqt⟩ := hKc.exists_bound_of_continuousOn (hqtcont.mono hsubK)
  obtain ⟨Ch0, hCh0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont_h t)
  obtain ⟨Cq0, hCq0⟩ := isCompact_Icc.exists_bound_of_continuousOn (hcont_q t)
  have hmemK0 : (t, 0) ∈ Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc 0 L :=
    Set.mk_mem_prod ⟨by linarith, by linarith⟩ ⟨le_rfl, h0L⟩
  have hCht0 : 0 ≤ Cht := le_trans (norm_nonneg _) (hCht _ hmemK0)
  have hCqt0 : 0 ≤ Cqt := le_trans (norm_nonneg _) (hCqt _ hmemK0)
  have hCh00 : 0 ≤ Ch0 := le_trans (norm_nonneg _) (hCh0 _ ⟨le_rfl, h0L⟩)
  have hCq00 : 0 ≤ Cq0 := le_trans (norm_nonneg _) (hCq0 _ ⟨le_rfl, h0L⟩)
  have hBh0 : 0 ≤ Ch0 + Cht * 1 := add_nonneg hCh00 (mul_nonneg hCht0 zero_le_one)
  have hBq0 : 0 ≤ Cq0 + Cqt * 1 := add_nonneg hCq00 (mul_nonneg hCqt0 zero_le_one)
  have ht_mem : t ∈ Set.Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hLip_h : ∀ x ∈ Set.Icc 0 L, ∀ s ∈ Set.Icc (t - 1) (t + 1),
      ‖h s x - h t x‖ ≤ Cht * 1 := by
    intro x hxIcc s hs
    have h1 : ‖h s x - h t x‖ ≤ Cht * ‖s - t‖ :=
      (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u _ => (hht u x hxIcc).hasDerivWithinAt)
        (fun u hu => hCht _ (Set.mk_mem_prod hu hxIcc)) ht_mem hs
    have hst : ‖s - t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.1, hs.2]
    calc ‖h s x - h t x‖ ≤ Cht * ‖s - t‖ := h1
      _ ≤ Cht * 1 := mul_le_mul_of_nonneg_left hst hCht0
  have hLip_q : ∀ x ∈ Set.Icc 0 L, ∀ s ∈ Set.Icc (t - 1) (t + 1),
      ‖q s x - q t x‖ ≤ Cqt * 1 := by
    intro x hxIcc s hs
    have h1 : ‖q s x - q t x‖ ≤ Cqt * ‖s - t‖ :=
      (convex_Icc _ _).norm_image_sub_le_of_norm_hasDerivWithin_le
        (fun u _ => (hqt u x hxIcc).hasDerivWithinAt)
        (fun u hu => hCqt _ (Set.mk_mem_prod hu hxIcc)) ht_mem hs
    have hst : ‖s - t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.1, hs.2]
    calc ‖q s x - q t x‖ ≤ Cqt * ‖s - t‖ := h1
      _ ≤ Cqt * 1 := mul_le_mul_of_nonneg_left hst hCqt0
  have hBh : ∀ x ∈ Set.Icc 0 L, ∀ s ∈ Set.Icc (t - 1) (t + 1),
      ‖h s x‖ ≤ Ch0 + Cht * 1 := by
    intro x hxIcc s hs
    have htri : ‖h s x‖ ≤ ‖h t x‖ + ‖h s x - h t x‖ := by
      have hle := norm_add_le (h t x) (h s x - h t x)
      rwa [show h t x + (h s x - h t x) = h s x by ring] at hle
    exact le_trans htri (add_le_add (hCh0 _ hxIcc) (hLip_h x hxIcc s hs))
  have hBq : ∀ x ∈ Set.Icc 0 L, ∀ s ∈ Set.Icc (t - 1) (t + 1),
      ‖q s x‖ ≤ Cq0 + Cqt * 1 := by
    intro x hxIcc s hs
    have htri : ‖q s x‖ ≤ ‖q t x‖ + ‖q s x - q t x‖ := by
      have hle := norm_add_le (q t x) (q s x - q t x)
      rwa [show q t x + (q s x - q t x) = q s x by ring] at hle
    exact le_trans htri (add_le_add (hCq0 _ hxIcc) (hLip_q x hxIcc s hs))
  have hFpcont : ContinuousOn
      (fun x => (g * A / a^2) * ((h t x) * (ht t x))
        + ((q t x) * (qt t x)) / (g * A))
      (Set.Icc 0 L) := by
    have hh := hcont_h t
    have hq := hcont_q t
    have hth := hcont_ht t
    have htq := hcont_qt t
    fun_prop
  have hFpmeas : AEStronglyMeasurable
      (fun x => (g * A / a^2) * ((h t x) * (ht t x))
        + ((q t x) * (qt t x)) / (g * A))
      (volume.restrict (Set.uIoc 0 L)) :=
    (hFpcont.mono hsub).aestronglyMeasurable measurableSet_uIoc
  have hbound : ∀ x : ℝ, x ∈ Set.uIoc 0 L → ∀ s ∈ Set.Icc (t - 1) (t + 1),
      ‖(g * A / a^2) * ((h s x) * (ht s x)) + ((q s x) * (qt s x)) / (g * A)‖
        ≤ (g * A / a^2) * ((Ch0 + Cht * 1) * Cht)
          + ((Cq0 + Cqt * 1) * Cqt) / (g * A) := by
    intro x hx s hs
    have hxIcc := hsub hx
    have hh := hBh x hxIcc s hs
    have hq := hBq x hxIcc s hs
    have hhtb : ‖ht s x‖ ≤ Cht := hCht _ (Set.mk_mem_prod hs hxIcc)
    have hqtb : ‖qt s x‖ ≤ Cqt := hCqt _ (Set.mk_mem_prod hs hxIcc)
    have e1 : ‖(g * A / a^2) * ((h s x) * (ht s x))‖
        ≤ (g * A / a^2) * ((Ch0 + Cht * 1) * Cht) := by
      rw [norm_mul, norm_mul, Real.norm_eq_abs (g * A / a^2), abs_of_pos hc1]
      have hmul : ‖h s x‖ * ‖ht s x‖ ≤ (Ch0 + Cht * 1) * Cht :=
        le_trans (mul_le_mul_of_nonneg_right hh (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hhtb hBh0)
      exact mul_le_mul_of_nonneg_left hmul hc1.le
    have e2 : ‖((q s x) * (qt s x)) / (g * A)‖
        ≤ ((Cq0 + Cqt * 1) * Cqt) / (g * A) := by
      rw [norm_div, Real.norm_eq_abs (g * A), abs_of_pos hgA, norm_mul,
        div_le_div_iff_of_pos_right hgA]
      exact le_trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hqtb hBq0)
    exact le_trans (norm_add_le _ _) (add_le_add e1 e2)
  have hs : Set.Icc (t - 1) (t + 1) ∈ nhds t :=
    Icc_mem_nhds_iff.mpr ⟨by linarith, by linarith⟩
  have hdiff : ∀ x : ℝ, x ∈ Set.uIoc 0 L → ∀ s ∈ Set.Icc (t - 1) (t + 1),
      HasDerivAt
        (fun s => (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
        ((g * A / a^2) * ((h s x) * (ht s x))
          + ((q s x) * (qt s x)) / (g * A)) s := by
    intro x hx s _
    have hxIcc := hsub hx
    have dh := hht s x hxIcc
    have dq := hqt s x hxIcc
    have hsq : HasDerivAt (fun s => (h s x)^2)
        ((ht s x) * (h s x) + (h s x) * (ht s x)) s := by
      have hmul := dh.mul dh
      have hfun : (fun s => h s x) * (fun s => h s x) = fun s => (h s x)^2 := by
        funext u; simp [Pi.mul_apply, pow_two]
      rw [hfun] at hmul
      exact hmul
    have qsq : HasDerivAt (fun s => (q s x)^2)
        ((qt s x) * (q s x) + (q s x) * (qt s x)) s := by
      have hmul := dq.mul dq
      have hfun : (fun s => q s x) * (fun s => q s x) = fun s => (q s x)^2 := by
        funext u; simp [Pi.mul_apply, pow_two]
      rw [hfun] at hmul
      exact hmul
    have e1 : HasDerivAt (fun s => (g * A / a^2) * (h s x)^2 / 2)
        ((g * A / a^2) * ((ht s x) * (h s x) + (h s x) * (ht s x)) / 2) s :=
      hsq.const_mul (g * A / a^2) |>.div_const 2
    have e2 : HasDerivAt (fun s => (q s x)^2 / (2 * g * A))
        (((qt s x) * (q s x) + (q s x) * (qt s x)) / (2 * g * A)) s :=
      qsq.div_const (2 * g * A)
    have hadd : HasDerivAt
        (fun s => (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
        ((g * A / a^2) * ((ht s x) * (h s x) + (h s x) * (ht s x)) / 2
          + ((qt s x) * (q s x) + (q s x) * (qt s x)) / (2 * g * A)) s :=
      e1.add e2
    have hDeq : (g * A / a^2) * ((ht s x) * (h s x) + (h s x) * (ht s x)) / 2
          + ((qt s x) * (q s x) + (q s x) * (qt s x)) / (2 * g * A)
        = (g * A / a^2) * ((h s x) * (ht s x))
          + ((q s x) * (qt s x)) / (g * A) := by
      field_simp
      ring
    rw [hDeq] at hadd
    exact hadd
  have hboundint : IntervalIntegrable
      (fun _ : ℝ => (g * A / a^2) * ((Ch0 + Cht * 1) * Cht)
        + ((Cq0 + Cqt * 1) * Cqt) / (g * A)) volume 0 L :=
    intervalIntegrable_const
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
    (F' := fun s x => (g * A / a^2) * ((h s x) * (ht s x))
      + ((q s x) * (qt s x)) / (g * A))
    (bound := fun _ : ℝ => (g * A / a^2) * ((Ch0 + Cht * 1) * Cht)
      + ((Cq0 + Cqt * 1) * Cqt) / (g * A))
    (s := Set.Icc (t - 1) (t + 1))
    hs hFmeas hFint hFpmeas
    (Filter.Eventually.of_forall hbound) hboundint
    (Filter.Eventually.of_forall hdiff)
  obtain ⟨hFpint_raw, hderiv_raw⟩ := key
  have hFpint : IntervalIntegrable
      (fun x => (g * A / a^2) * ((h t x) * (ht t x))
        + ((q t x) * (qt t x)) / (g * A)) volume 0 L := hFpint_raw
  have hderiv : HasDerivAt
      (fun s => ∫ x in (0:ℝ)..L,
        (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
      (∫ x in (0:ℝ)..L, (g * A / a^2) * ((h t x) * (ht t x))
        + ((q t x) * (qt t x)) / (g * A)) t := hderiv_raw
  have hG : ∀ x ∈ Set.Icc 0 L, HasDerivAt (fun x => h t x * q t x)
      ((hx t x) * (q t x) + (h t x) * (qx t x)) x := by
    intro x hx
    have hmul := (hhx t x hx).mul (hqx t x hx)
    have hfun : (h t) * (q t) = fun x => h t x * q t x := by funext u; simp [Pi.mul_apply]
    rw [hfun] at hmul
    exact hmul
  have hGcont : ContinuousOn (fun x => h t x * q t x) (Set.Icc 0 L) :=
    HasDerivAt.continuousOn hG
  have hFpeq : ∀ x ∈ Set.Icc 0 L,
      (g * A / a^2) * ((h t x) * (ht t x)) + ((q t x) * (qt t x)) / (g * A)
        = -((hx t x) * (q t x) + (h t x) * (qx t x)) := by
    intro x hxIcc
    have ht_eq : ht t x = -((a^2 / (g * A)) * (qx t x)) := by
      linarith [hpde1 t x hxIcc]
    have qt_eq : qt t x = -((g * A) * (hx t x)) := by
      linarith [hpde2 t x hxIcc]
    rw [ht_eq, qt_eq]
    field_simp
    ring
  have hGpint : IntervalIntegrable
      (fun x => (hx t x) * (q t x) + (h t x) * (qx t x)) volume 0 L := by
    have hneg := hFpint.neg
    refine hneg.congr (fun x hx => ?_)
    have hxIcc := hsub hx
    simp only [Pi.neg_apply]
    rw [hFpeq x hxIcc]
    ring
  have hftc : (∫ x in (0:ℝ)..L, (hx t x) * (q t x) + (h t x) * (qx t x))
      = (h t L * q t L) - (h t 0 * q t 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0L hGcont
      (fun x hx => hG x (Set.mem_Icc_of_Ioo hx)) hGpint
  have hIcong : (∫ x in (0:ℝ)..L, (g * A / a^2) * ((h t x) * (ht t x))
        + ((q t x) * (qt t x)) / (g * A))
      = ∫ x in (0:ℝ)..L, -((hx t x) * (q t x) + (h t x) * (qx t x)) :=
    intervalIntegral.integral_congr_ae
      (Filter.Eventually.of_forall fun x hx => hFpeq x (hsub hx))
  have hIneg : (∫ x in (0:ℝ)..L, -((hx t x) * (q t x) + (h t x) * (qx t x)))
      = -∫ x in (0:ℝ)..L, (hx t x) * (q t x) + (h t x) * (qx t x) :=
    intervalIntegral.integral_neg
  have hIntEq : (∫ x in (0:ℝ)..L, (g * A / a^2) * ((h t x) * (ht t x))
        + ((q t x) * (qt t x)) / (g * A))
      = h t 0 * q t 0 - h t L * q t L := by
    rw [hIcong, hIneg, hftc]
    ring
  rw [hIntEq] at hderiv
  exact hderiv

end WaterHammerEnergy
