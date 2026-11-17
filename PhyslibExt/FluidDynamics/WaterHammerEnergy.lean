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

theorem time_bound_of_deriv_bound {f df : ℝ → ℝ → ℝ} {t L M0 M1 : ℝ}
    (hf : ∀ s x : ℝ, x ∈ Set.Icc 0 L → HasDerivAt (fun s => f s x) (df s x) s)
    (hM1 : ∀ s x : ℝ, s ∈ Set.Icc (t - 1) (t + 1) → x ∈ Set.Icc 0 L → ‖df s x‖ ≤ M1)
    (hM10 : 0 ≤ M1)
    (hM0 : ∀ x : ℝ, x ∈ Set.Icc 0 L → ‖f t x‖ ≤ M0)
    (x : ℝ) (hx : x ∈ Set.Icc 0 L) (s : ℝ) (hs : s ∈ Set.Icc (t - 1) (t + 1)) :
    ‖f s x‖ ≤ M0 + M1 := by
  have htS : t ∈ Set.Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hdiff : ∀ s' ∈ Set.Icc (t - 1) (t + 1), DifferentiableAt ℝ (fun s => f s x) s' :=
    fun s' _ => (hf s' x hx).differentiableAt
  have hdb : ∀ s' ∈ Set.Icc (t - 1) (t + 1), ‖deriv (fun s => f s x) s'‖ ≤ M1 := by
    intro s' hs'
    rw [(hf s' x hx).deriv]
    exact hM1 s' x hs' hx
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hdb (convex_Icc _ _) htS hs
  have hst1 : ‖s - t‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hs.1, hs.2]
  have e : f t x + (f s x - f t x) = f s x := by ring
  calc ‖f s x‖ = ‖f t x + (f s x - f t x)‖ := by rw [e]
    _ ≤ ‖f t x‖ + ‖f s x - f t x‖ := norm_add_le _ _
    _ ≤ M0 + M1 * ‖s - t‖ := add_le_add (hM0 x hx) hmvt
    _ ≤ M0 + M1 * 1 := add_le_add le_rfl (mul_le_mul_of_nonneg_left hst1 hM10)
    _ = M0 + M1 := by rw [mul_one]

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
    (hint : ∀ t : ℝ, IntervalIntegrable
      (fun x => (g * A / a^2) * (h t x)^2 / 2 + (q t x)^2 / (2 * g * A))
      MeasureTheory.volume 0 L)
    (hcont : ∀ t : ℝ, ContinuousOn (fun x => h t x * q t x) (Set.Icc 0 L))
    (hhtcont : ContinuousOn (fun p : ℝ × ℝ => ht p.1 p.2)
      (Set.univ ×ˢ Set.Icc 0 L))
    (hqtcont : ContinuousOn (fun p : ℝ × ℝ => qt p.1 p.2)
      (Set.univ ×ˢ Set.Icc 0 L))
    (t : ℝ) :
    HasDerivAt (fun s => ∫ x in (0:ℝ)..L,
        (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
      (h t 0 * q t 0 - h t L * q t L) t := by
  have hga : (0:ℝ) < g * A := mul_pos hg hA
  have hga_ne : g * A ≠ 0 := ne_of_gt hga
  have ha_ne : a ≠ 0 := ne_of_gt ha
  have ha2_ne : a ^ 2 ≠ 0 := pow_ne_zero 2 ha_ne
  have h0L : (0:ℝ) ≤ L := hL.le
  have huIoc : Set.uIoc 0 L = Set.Ioc 0 L := Set.uIoc_of_le h0L
  have hs : Set.Icc (t - 1) (t + 1) ∈ nhds t := Icc_mem_nhds (by linarith) (by linarith)
  have htS : t ∈ Set.Icc (t - 1) (t + 1) := ⟨by linarith, by linarith⟩
  have hKc : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc 0 L) :=
    isCompact_Icc.prod isCompact_Icc
  have hKsub : Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc 0 L ⊆ Set.univ ×ˢ Set.Icc 0 L := by
    intro p hp
    exact ⟨Set.mem_univ _, hp.2⟩
  obtain ⟨Mht, hMht⟩ := hKc.exists_bound_of_continuousOn (hhtcont.mono hKsub)
  obtain ⟨Mqt, hMqt⟩ := hKc.exists_bound_of_continuousOn (hqtcont.mono hKsub)
  have hmemK : (t, 0) ∈ Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc 0 L :=
    ⟨htS, le_rfl, hL.le⟩
  have hMht0 : 0 ≤ Mht := le_trans (norm_nonneg _) (hMht _ hmemK)
  have hMqt0 : 0 ≤ Mqt := le_trans (norm_nonneg _) (hMqt _ hmemK)
  have hhcont : ContinuousOn (fun x => h t x) (Set.Icc 0 L) :=
    continuousOn_of_forall_continuousAt (fun x hx => (hhx t x hx).continuousAt)
  have hqcont : ContinuousOn (fun x => q t x) (Set.Icc 0 L) :=
    continuousOn_of_forall_continuousAt (fun x hx => (hqx t x hx).continuousAt)
  obtain ⟨Mh0, hMh0⟩ := isCompact_Icc.exists_bound_of_continuousOn hhcont
  obtain ⟨Mq0, hMq0⟩ := isCompact_Icc.exists_bound_of_continuousOn hqcont
  have hMh00 : 0 ≤ Mh0 := le_trans (norm_nonneg _) (hMh0 0 ⟨le_rfl, hL.le⟩)
  have hMq00 : 0 ≤ Mq0 := le_trans (norm_nonneg _) (hMq0 0 ⟨le_rfl, hL.le⟩)
  have hHbound : ∀ x ∈ Set.Icc 0 L, ∀ s ∈ Set.Icc (t - 1) (t + 1), ‖h s x‖ ≤ Mh0 + Mht :=
    fun x hx s hs' => time_bound_of_deriv_bound (f := h) (df := ht) (t := t) (L := L)
      (M0 := Mh0) (M1 := Mht) hht (fun s x hs'' hx' => hMht (s, x) ⟨hs'', hx'⟩)
      hMht0 (fun x hx' => hMh0 x hx') x hx s hs'
  have hQbound : ∀ x ∈ Set.Icc 0 L, ∀ s ∈ Set.Icc (t - 1) (t + 1), ‖q s x‖ ≤ Mq0 + Mqt :=
    fun x hx s hs' => time_bound_of_deriv_bound (f := q) (df := qt) (t := t) (L := L)
      (M0 := Mq0) (M1 := Mqt) hqt (fun s x hs'' hx' => hMqt (s, x) ⟨hs'', hx'⟩)
      hMqt0 (fun x hx' => hMq0 x hx') x hx s hs'
  set M : ℝ := ‖(g * A / a ^ 2)‖ * (Mh0 + Mht) * Mht + (Mq0 + Mqt) * Mqt * ‖(g * A)⁻¹‖ with hMdef
  have h_diff : ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 L → ∀ s ∈ Set.Icc (t - 1) (t + 1),
      HasDerivAt (fun s' => (g * A / a ^ 2) * (h s' x) ^ 2 / 2 + (q s' x) ^ 2 / (2 * g * A))
        ((g * A / a ^ 2) * (h s x) * (ht s x) + (q s x) * (qt s x) / (g * A)) s := by
    refine ae_of_all _ (fun x hx s _ => ?_)
    rw [huIoc] at hx
    have hxIcc : x ∈ Set.Icc 0 L := Set.Ioc_subset_Icc_self hx
    have hpow : HasDerivAt (fun s' => (h s' x) ^ 2) (2 * h s x * ht s x) s := by
      have hrw : (2:ℝ) * h s x * ht s x = ht s x * h s x + h s x * ht s x := by ring
      rw [hrw]
      simp only [pow_two]
      exact (hht s x hxIcc).mul (hht s x hxIcc)
    have qpow : HasDerivAt (fun s' => (q s' x) ^ 2) (2 * q s x * qt s x) s := by
      have hrw : (2:ℝ) * q s x * qt s x = qt s x * q s x + q s x * qt s x := by ring
      rw [hrw]
      simp only [pow_two]
      exact (hqt s x hxIcc).mul (hqt s x hxIcc)
    have hterm : HasDerivAt (fun s' => (g * A / a ^ 2) * (h s' x) ^ 2 / 2)
        ((g * A / a ^ 2) * (h s x) * (ht s x)) s := by
      have e := (hpow.const_mul (g * A / a ^ 2)).div_const 2
      have hrw : (g * A / a ^ 2) * (h s x) * (ht s x)
          = (g * A / a ^ 2) * (2 * h s x * ht s x) / 2 := by ring
      rw [hrw]
      exact e
    have h2ga : (2:ℝ) * g * A ≠ 0 := by
      have h2 : (2:ℝ) * (g * A) = 2 * g * A := by ring
      rw [← h2]
      exact mul_ne_zero two_ne_zero hga_ne
    have qterm : HasDerivAt (fun s' => (q s' x) ^ 2 / (2 * g * A))
        ((q s x) * (qt s x) / (g * A)) s := by
      have e := qpow.div_const (2 * g * A)
      have hrw : (q s x) * (qt s x) / (g * A) = (2 * q s x * qt s x) / (2 * g * A) := by
        field_simp
      rw [hrw]
      exact e
    exact hterm.add qterm
  have hF_meas : ∀ᶠ s' in nhds t, AEStronglyMeasurable
      (fun x => (g * A / a ^ 2) * (h s' x) ^ 2 / 2 + (q s' x) ^ 2 / (2 * g * A))
      (volume.restrict (Set.uIoc 0 L)) := by
    refine Filter.Eventually.of_forall (fun s' => ?_)
    rw [huIoc]
    exact (hint s').aestronglyMeasurable
  have hF_int : IntervalIntegrable
      (fun x => (g * A / a ^ 2) * (h t x) ^ 2 / 2 + (q t x) ^ 2 / (2 * g * A))
      volume 0 L := hint t
  have hprod : ContinuousOn (fun x : ℝ => (t, x)) (Set.Icc 0 L) :=
    continuousOn_const.prodMk continuousOn_id
  have hmaps : Set.MapsTo (fun x : ℝ => (t, x)) (Set.Icc 0 L) (Set.univ ×ˢ Set.Icc 0 L) :=
    fun x hx => ⟨Set.mem_univ _, hx⟩
  have hht_t : ContinuousOn (fun x => ht t x) (Set.Icc 0 L) := hhtcont.comp hprod hmaps
  have hqt_t : ContinuousOn (fun x => qt t x) (Set.Icc 0 L) := hqtcont.comp hprod hmaps
  have hF'_meas : AEStronglyMeasurable
      (fun x => (g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A))
      (volume.restrict (Set.uIoc 0 L)) := by
    rw [huIoc]
    have hbig : ContinuousOn
        (fun x => (g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A))
        (Set.Icc 0 L) :=
      (((hhcont.const_mul _).mul hht_t).add ((hqcont.mul hqt_t).div_const _))
    exact (hbig.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have h_bound : ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 L → ∀ s ∈ Set.Icc (t - 1) (t + 1),
      ‖(g * A / a ^ 2) * (h s x) * (ht s x) + (q s x) * (qt s x) / (g * A)‖ ≤ M := by
    refine ae_of_all _ (fun x hx s hs' => ?_)
    rw [huIoc] at hx
    have hxIcc : x ∈ Set.Icc 0 L := Set.Ioc_subset_Icc_self hx
    have hH := hHbound x hxIcc s hs'
    have hQ := hQbound x hxIcc s hs'
    have hHt : ‖ht s x‖ ≤ Mht := hMht (s, x) ⟨hs', hxIcc⟩
    have hQt : ‖qt s x‖ ≤ Mqt := hMqt (s, x) ⟨hs', hxIcc⟩
    have h1 : ‖(g * A / a ^ 2) * (h s x) * (ht s x)‖
        ≤ ‖(g * A / a ^ 2)‖ * (Mh0 + Mht) * Mht := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul le_rfl hH (norm_nonneg _) (norm_nonneg _)) hHt
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (add_nonneg hMh00 hMht0))
    have h2 : ‖(q s x) * (qt s x) / (g * A)‖ ≤ (Mq0 + Mqt) * Mqt * ‖(g * A)⁻¹‖ := by
      rw [div_eq_mul_inv, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul hQ hQt (norm_nonneg _) (add_nonneg hMq00 hMqt0)) (norm_nonneg _)
    have h12 := add_le_add h1 h2
    rw [← hMdef] at h12
    exact (norm_add_le _ _).trans h12
  have hbound_int : IntervalIntegrable (fun _ => M) volume 0 L := intervalIntegrable_const
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s x => (g * A / a ^ 2) * (h s x) ^ 2 / 2 + (q s x) ^ 2 / (2 * g * A))
    (F' := fun s x => (g * A / a ^ 2) * (h s x) * (ht s x) + (q s x) * (qt s x) / (g * A))
    (bound := fun _ => M) (x₀ := t) (s := Set.Icc (t - 1) (t + 1))
    hs hF_meas hF_int hF'_meas h_bound hbound_int h_diff
  have hFt_int : IntervalIntegrable
      (fun x => (g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A))
      volume 0 L := hmain.1
  have hmain2 : HasDerivAt
      (fun s => ∫ x in (0:ℝ)..L, (g * A / a ^ 2) * (h s x) ^ 2 / 2 + (q s x) ^ 2 / (2 * g * A))
      (∫ x in (0:ℝ)..L, (g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A))
      t := hmain.2
  have hFeq : ∀ x ∈ Set.Icc 0 L,
      (g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A)
        = -((hx t x) * (q t x) + (h t x) * (qx t x)) := by
    intro x hxIcc
    have e1 := hpde1 t x hxIcc
    have e2 := hpde2 t x hxIcc
    have ht_eq : ht t x = -((a ^ 2 / (g * A)) * qx t x) := by linarith
    have qt_eq : qt t x = -((g * A) * hx t x) := by linarith
    rw [ht_eq, qt_eq]
    field_simp
    ring
  have hderivIoo : ∀ x ∈ Set.Ioo 0 L,
      HasDerivAt (fun x => h t x * q t x) ((hx t x) * (q t x) + (h t x) * (qx t x)) x :=
    fun x hx => (hhx t x (Set.Ioo_subset_Icc_self hx)).mul (hqx t x (Set.Ioo_subset_Icc_self hx))
  have hneg_int : IntervalIntegrable
      (-(fun x => (g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A)))
      volume 0 L := hFt_int.neg
  have heq : Set.EqOn
      (-(fun x => (g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A)))
      (fun x => (hx t x) * (q t x) + (h t x) * (qx t x)) (Set.uIoc 0 L) := by
    intro x hxu
    rw [huIoc] at hxu
    have hxIcc : x ∈ Set.Icc 0 L := Set.Ioc_subset_Icc_self hxu
    have hFeqx := hFeq x hxIcc
    show -((g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A))
      = (hx t x) * (q t x) + (h t x) * (qx t x)
    rw [hFeqx, neg_neg]
  have hf'_int : IntervalIntegrable
      (fun x => (hx t x) * (q t x) + (h t x) * (qx t x)) volume 0 L :=
    IntervalIntegrable.congr heq hneg_int
  have hFTC : (∫ x in (0:ℝ)..L, (hx t x) * (q t x) + (h t x) * (qx t x))
      = (h t L) * (q t L) - (h t 0) * (q t 0) :=
    integral_eq_sub_of_hasDerivAt_of_le h0L (hcont t) hderivIoo hf'_int
  have hIntEq : (∫ x in (0:ℝ)..L, (g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A))
      = h t 0 * q t 0 - h t L * q t L := by
    have hae : ∀ᵐ x ∂volume, x ∈ Set.uIoc 0 L →
        (g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A)
          = -((hx t x) * (q t x) + (h t x) * (qx t x)) := by
      refine ae_of_all _ (fun x hx => ?_)
      rw [huIoc] at hx
      exact hFeq x (Set.Ioc_subset_Icc_self hx)
    calc (∫ x in (0:ℝ)..L, (g * A / a ^ 2) * (h t x) * (ht t x) + (q t x) * (qt t x) / (g * A))
          = ∫ x in (0:ℝ)..L, -((hx t x) * (q t x) + (h t x) * (qx t x)) :=
            integral_congr_ae hae
        _ = -(∫ x in (0:ℝ)..L, (hx t x) * (q t x) + (h t x) * (qx t x)) := integral_neg
        _ = -((h t L) * (q t L) - (h t 0) * (q t 0)) := by rw [hFTC]
        _ = h t 0 * q t 0 - h t L * q t L := by ring
  rw [hIntEq] at hmain2
  exact hmain2

end WaterHammerEnergy
