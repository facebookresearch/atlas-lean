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

- `FluidDynamics.WaterHammerEnergy.energy_hasDerivAt`: the flux identity.

## iii. Table of contents

- A. Energy flux

## iv. References

- E. B. Wylie and V. L. Streeter, *Fluid Transients in Systems*,
  Prentice Hall, 1993 (water-hammer energy balance).

## A. Energy flux
-/

@[expose] public section

namespace FluidDynamics.WaterHammerEnergy

open MeasureTheory intervalIntegral

private lemma bound_of_contOn {X : Type*} [TopologicalSpace X] {f : X → ℝ} {K : Set X}
    (hK : IsCompact K) (hf : ContinuousOn f K) :
    ∃ M, 0 ≤ M ∧ ∀ x ∈ K, ‖f x‖ ≤ M := by
  obtain ⟨C, hC⟩ := (hK.image_of_continuousOn hf).isBounded.exists_norm_le
  have hC' : ∀ x, x ∈ f '' K → ‖x‖ ≤ C := hC
  exact ⟨|C|, abs_nonneg C, fun x hx => (hC' _ ⟨x, hx, rfl⟩).trans (le_abs_self C)⟩

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
    (hhx : ∀ t x : ℝ, x ∈ Set.Icc 0 L →
      HasDerivWithinAt (h t) (hx t x) (Set.Icc 0 L) x)
    (hqx : ∀ t x : ℝ, x ∈ Set.Icc 0 L →
      HasDerivWithinAt (q t) (qx t x) (Set.Icc 0 L) x)
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
  have h0L : (0:ℝ) ≤ L := le_of_lt hL
  have ha2' : (a:ℝ)^2 ≠ 0 := by positivity
  have hgA : g * A ≠ 0 := by positivity
  have hC2 : (2:ℝ) * g * A ≠ 0 := by positivity
  have conth : ∀ s : ℝ, ContinuousOn (h s) (Set.Icc 0 L) :=
    fun s x hx => (hhx s x hx).continuousWithinAt
  have contq : ∀ s : ℝ, ContinuousOn (q s) (Set.Icc 0 L) :=
    fun s x hx => (hqx s x hx).continuousWithinAt
  have contHt : ContinuousOn (fun x => ht t x) (Set.Icc 0 L) := by
    have hpair : ContinuousOn (fun x : ℝ => (t, x)) (Set.Icc 0 L) :=
      continuousOn_const.prodMk continuousOn_id
    have h := hhtcont.comp hpair (fun x hx => Set.mk_mem_prod (Set.mem_univ _) hx)
    exact h
  have contQt : ContinuousOn (fun x => qt t x) (Set.Icc 0 L) := by
    have hpair : ContinuousOn (fun x : ℝ => (t, x)) (Set.Icc 0 L) :=
      continuousOn_const.prodMk continuousOn_id
    have h := hqtcont.comp hpair (fun x hx => Set.mk_mem_prod (Set.mem_univ _) hx)
    exact h
  have hx_eq : ∀ x ∈ Set.Icc 0 L, hx t x = (-(qt t x)) / (g * A) := by
    intro x hx
    rw [eq_div_iff hgA]
    linear_combination (hpde2 t x hx)
  have contHx : ContinuousOn (fun x => hx t x) (Set.Icc 0 L) :=
    ((contQt.neg).div continuousOn_const (fun _ _ => hgA)).congr (fun x hx => hx_eq x hx)
  have hc : (a:ℝ)^2 / (g * A) ≠ 0 := div_ne_zero ha2' hgA
  have qx_eq : ∀ x ∈ Set.Icc 0 L, qx t x = (-(ht t x)) / (a^2 / (g * A)) := by
    intro x hx
    rw [eq_div_iff hc]
    linear_combination (hpde1 t x hx)
  have contQx : ContinuousOn (fun x => qx t x) (Set.Icc 0 L) :=
    ((contHt.neg).div continuousOn_const (fun _ _ => hc)).congr (fun x hx => qx_eq x hx)
  have contP : ContinuousOn (fun x => hx t x * q t x + h t x * qx t x) (Set.Icc 0 L) :=
    (contHx.mul (contq t)).add ((conth t).mul contQx)
  have contHQ : ContinuousOn (fun x => h t x * q t x) (Set.Icc 0 L) :=
    (conth t).mul (contq t)
  have hderivP : ∀ x ∈ Set.Ioo 0 L,
      HasDerivAt (fun x => h t x * q t x) (hx t x * q t x + h t x * qx t x) x := by
    intro x hxmem
    have hxI : x ∈ Set.Icc 0 L := Set.Ioo_subset_Icc_self hxmem
    have h1 : HasDerivAt (h t) (hx t x) x := (hhx t x hxI).hasDerivAt (Icc_mem_nhds hxmem.1 hxmem.2)
    have h2 : HasDerivAt (q t) (qx t x) x := (hqx t x hxI).hasDerivAt (Icc_mem_nhds hxmem.1 hxmem.2)
    exact h1.fun_mul h2
  have hintP : IntervalIntegrable (fun x => hx t x * q t x + h t x * qx t x) volume 0 L :=
    contP.intervalIntegrable_of_Icc h0L
  have hFTC : (∫ x in (0:ℝ)..L, hx t x * q t x + h t x * qx t x)
      = h t L * q t L - h t 0 * q t 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h0L contHQ hderivP hintP
  have contF : ∀ s : ℝ, ContinuousOn
      (fun x => (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
      (Set.Icc 0 L) := by
    intro s
    simp only [pow_two]
    exact ((((conth s).mul (conth s)).const_mul _).div continuousOn_const
      (fun _ _ => two_ne_zero)).add
      (((contq s).mul (contq s)).div continuousOn_const (fun _ _ => hC2))
  have contD : ContinuousOn
      (fun x => (g * A / a^2) * (ht t x * h t x + h t x * ht t x) / 2
        + (qt t x * q t x + q t x * qt t x) / (2 * g * A))
      (Set.Icc 0 L) :=
    ((((contHt.mul (conth t)).add ((conth t).mul contHt)).const_mul _).div
      continuousOn_const (fun _ _ => two_ne_zero)).add
      (((contQt.mul (contq t)).add ((contq t).mul contQt)).div
        continuousOn_const (fun _ _ => hC2))
  have hK : IsCompact (Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc 0 L) :=
    isCompact_Icc.prod isCompact_Icc
  have hsub : Set.Icc (t - 1) (t + 1) ×ˢ Set.Icc 0 L ⊆ Set.univ ×ˢ Set.Icc 0 L := by
    rintro ⟨u, x⟩ hp
    obtain ⟨-, hx⟩ := hp
    show (u, x) ∈ Set.univ ×ˢ Set.Icc 0 L
    exact Set.mk_mem_prod (Set.mem_univ _) hx
  obtain ⟨Mht, hMhtnn, hMht⟩ := bound_of_contOn hK (hhtcont.mono hsub)
  obtain ⟨Mqt, hMqtnn, hMqt⟩ := bound_of_contOn hK (hqtcont.mono hsub)
  obtain ⟨Mh0, hMh0nn, hMh0⟩ := bound_of_contOn isCompact_Icc (conth t)
  obtain ⟨Mq0, hMq0nn, hMq0⟩ := bound_of_contOn isCompact_Icc (contq t)
  have hbound_h : ∀ s ∈ Metric.ball t 1, ∀ x ∈ Set.Icc 0 L, ‖h s x‖ ≤ Mh0 + Mht := by
    intro s hs x hxI
    have hsI : s ∈ Set.Icc (t - 1) (t + 1) := by
      have h1 := hs
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at h1
      rw [Set.mem_Icc]
      constructor <;> linarith [h1.1, h1.2]
    have htI : t ∈ Set.Icc (t - 1) (t + 1) := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (hht u x hxI).hasDerivWithinAt)
      (fun u hu => hMht (u, x) (Set.mk_mem_prod hu hxI))
      (convex_Icc (t - 1) (t + 1)) htI hsI
    have hmv' : ‖h s x - h t x‖ ≤ Mht * ‖s - t‖ := hmv
    have hst : ‖s - t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      rw [Set.mem_Icc] at hsI
      constructor <;> linarith [hsI.1, hsI.2]
    have hM : Mht * ‖s - t‖ ≤ Mht := by
      have h := mul_le_mul_of_nonneg_left hst hMhtnn
      rwa [mul_one] at h
    have hsplit : ‖h s x‖ ≤ ‖h t x‖ + ‖h s x - h t x‖ := by
      have e : h s x = h t x + (h s x - h t x) := by ring
      conv_lhs => rw [e]
      exact norm_add_le _ _
    exact hsplit.trans (add_le_add (hMh0 x hxI) (hmv'.trans hM))
  have hbound_q : ∀ s ∈ Metric.ball t 1, ∀ x ∈ Set.Icc 0 L, ‖q s x‖ ≤ Mq0 + Mqt := by
    intro s hs x hxI
    have hsI : s ∈ Set.Icc (t - 1) (t + 1) := by
      have h1 := hs
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at h1
      rw [Set.mem_Icc]
      constructor <;> linarith [h1.1, h1.2]
    have htI : t ∈ Set.Icc (t - 1) (t + 1) := by
      rw [Set.mem_Icc]
      constructor <;> linarith
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun u _ => (hqt u x hxI).hasDerivWithinAt)
      (fun u hu => hMqt (u, x) (Set.mk_mem_prod hu hxI))
      (convex_Icc (t - 1) (t + 1)) htI hsI
    have hmv' : ‖q s x - q t x‖ ≤ Mqt * ‖s - t‖ := hmv
    have hst : ‖s - t‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      rw [Set.mem_Icc] at hsI
      constructor <;> linarith [hsI.1, hsI.2]
    have hM : Mqt * ‖s - t‖ ≤ Mqt := by
      have h := mul_le_mul_of_nonneg_left hst hMqtnn
      rwa [mul_one] at h
    have hsplit : ‖q s x‖ ≤ ‖q t x‖ + ‖q s x - q t x‖ := by
      have e : q s x = q t x + (q s x - q t x) := by ring
      conv_lhs => rw [e]
      exact norm_add_le _ _
    exact hsplit.trans (add_le_add (hMq0 x hxI) (hmv'.trans hM))
  have hDeriv : ∀ x ∈ Set.Icc 0 L, ∀ s : ℝ,
      HasDerivAt (fun s => (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
        ((g * A / a^2) * (ht s x * h s x + h s x * ht s x) / 2
          + (qt s x * q s x + q s x * qt s x) / (2 * g * A)) s := by
    intro x hxI s
    have h2 : HasDerivAt (fun s => (h s x)^2) (ht s x * h s x + h s x * ht s x) s := by
      simpa only [pow_two] using (hht s x hxI).fun_mul (hht s x hxI)
    have q2 : HasDerivAt (fun s => (q s x)^2) (qt s x * q s x + q s x * qt s x) s := by
      simpa only [pow_two] using (hqt s x hxI).fun_mul (hqt s x hxI)
    exact ((h2.const_mul _).div_const _).fun_add (q2.div_const _)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ s ∈ Metric.ball t 1, ∀ x ∈ Set.uIoc (0:ℝ) L,
      ‖(g * A / a^2) * (ht s x * h s x + h s x * ht s x) / 2
        + (qt s x * q s x + q s x * qt s x) / (2 * g * A)‖ ≤ M := by
    refine ⟨|g * A / a^2| * (Mht * (Mh0 + Mht) + (Mh0 + Mht) * Mht) / 2
      + (Mqt * (Mq0 + Mqt) + (Mq0 + Mqt) * Mqt) / |2 * g * A|, ?_⟩
    intro s hs x hx
    rw [Set.uIoc_of_le h0L] at hx
    have hxI : x ∈ Set.Icc 0 L := Set.Ioc_subset_Icc_self hx
    have hsI : s ∈ Set.Icc (t - 1) (t + 1) := by
      have h1 := hs
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at h1
      rw [Set.mem_Icc]
      constructor <;> linarith [h1.1, h1.2]
    have bht : ‖ht s x‖ ≤ Mht := hMht (s, x) (Set.mk_mem_prod hsI hxI)
    have bqt : ‖qt s x‖ ≤ Mqt := hMqt (s, x) (Set.mk_mem_prod hsI hxI)
    have bh : ‖h s x‖ ≤ Mh0 + Mht := hbound_h s hs x hxI
    have bq : ‖q s x‖ ≤ Mq0 + Mqt := hbound_q s hs x hxI
    have hD1 : ‖ht s x * h s x + h s x * ht s x‖
        ≤ Mht * (Mh0 + Mht) + (Mh0 + Mht) * Mht :=
      (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans
        (mul_le_mul bht bh (norm_nonneg _) hMhtnn)) ((norm_mul_le _ _).trans
        (mul_le_mul bh bht (norm_nonneg _) (add_nonneg hMh0nn hMhtnn))))
    have hD2 : ‖qt s x * q s x + q s x * qt s x‖
        ≤ Mqt * (Mq0 + Mqt) + (Mq0 + Mqt) * Mqt :=
      (norm_add_le _ _).trans (add_le_add ((norm_mul_le _ _).trans
        (mul_le_mul bqt bq (norm_nonneg _) hMqtnn)) ((norm_mul_le _ _).trans
        (mul_le_mul bq bqt (norm_nonneg _) (add_nonneg hMq0nn hMqtnn))))
    have eC1 : ‖g * A / a^2‖ = |g * A / a^2| := by rw [Real.norm_eq_abs]
    have eC2 : ‖(2:ℝ) * g * A‖ = |2 * g * A| := by rw [Real.norm_eq_abs]
    have e2 : ‖(2:ℝ)‖ = 2 := by rw [Real.norm_eq_abs]; norm_num
    have hC1D1 : ‖(g * A / a^2) * (ht s x * h s x + h s x * ht s x)‖
        ≤ |g * A / a^2| * (Mht * (Mh0 + Mht) + (Mh0 + Mht) * Mht) :=
      (norm_mul_le _ _).trans (by
        rw [eC1]
        exact mul_le_mul_of_nonneg_left hD1 (abs_nonneg _))
    have hT1 : ‖(g * A / a^2) * (ht s x * h s x + h s x * ht s x) / 2‖
        ≤ |g * A / a^2| * (Mht * (Mh0 + Mht) + (Mh0 + Mht) * Mht) / 2 := by
      rw [norm_div, e2]
      exact div_le_div_of_nonneg_right hC1D1 (by norm_num : (0:ℝ) ≤ 2)
    have hT2 : ‖(qt s x * q s x + q s x * qt s x) / (2 * g * A)‖
        ≤ (Mqt * (Mq0 + Mqt) + (Mq0 + Mqt) * Mqt) / |2 * g * A| := by
      rw [norm_div, eC2]
      exact div_le_div_of_nonneg_right hD2 (abs_nonneg _)
    exact (norm_add_le _ _).trans (add_le_add hT1 hT2)
  have F_meas : ∀ᶠ s in nhds t, AEStronglyMeasurable
      (fun x => (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
      (volume.restrict (Set.uIoc 0 L)) := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    rw [Set.uIoc_of_le h0L]
    exact ((contF s).mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have F_int : IntervalIntegrable
      (fun x => (g * A / a^2) * (h t x)^2 / 2 + (q t x)^2 / (2 * g * A))
      volume 0 L :=
    (contF t).intervalIntegrable_of_Icc h0L
  have F'_meas : AEStronglyMeasurable
      (fun x => (g * A / a^2) * (ht t x * h t x + h t x * ht t x) / 2
        + (qt t x * q t x + q t x * qt t x) / (2 * g * A))
      (volume.restrict (Set.uIoc 0 L)) := by
    rw [Set.uIoc_of_le h0L]
    exact (contD.mono Set.Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  have bound_int : IntervalIntegrable (fun _ => M) volume 0 L :=
    continuousOn_const.intervalIntegrable_of_Icc h0L
  have bound_le : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0:ℝ) L →
      ∀ s ∈ Metric.ball t 1,
        ‖(g * A / a^2) * (ht s x * h s x + h s x * ht s x) / 2
          + (qt s x * q s x + q s x * qt s x) / (2 * g * A)‖ ≤ M :=
    Filter.Eventually.of_forall (fun x hx s hs => hM s hs x hx)
  have F'_deriv : ∀ᵐ x ∂volume, x ∈ Set.uIoc (0:ℝ) L →
      ∀ s ∈ Metric.ball t 1,
        HasDerivAt (fun s => (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
          ((g * A / a^2) * (ht s x * h s x + h s x * ht s x) / 2
            + (qt s x * q s x + q s x * qt s x) / (2 * g * A)) s := by
    refine Filter.Eventually.of_forall (fun x hx s _ => ?_)
    rw [Set.uIoc_of_le h0L] at hx
    have hxI : x ∈ Set.Icc 0 L := Set.Ioc_subset_Icc_self hx
    exact hDeriv x hxI s
  have hleib := (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t zero_lt_one) F_meas F_int F'_meas bound_le bound_int F'_deriv).2
  have hleib2 : HasDerivAt
      (fun s => ∫ x in (0:ℝ)..L, (g * A / a^2) * (h s x)^2 / 2 + (q s x)^2 / (2 * g * A))
      (∫ x in (0:ℝ)..L, (g * A / a^2) * (ht t x * h t x + h t x * ht t x) / 2
        + (qt t x * q t x + q t x * qt t x) / (2 * g * A)) t := hleib
  have hkey : ∀ x ∈ Set.Icc 0 L,
      (g * A / a^2) * (ht t x * h t x + h t x * ht t x) / 2
        + (qt t x * q t x + q t x * qt t x) / (2 * g * A)
      = -(hx t x * q t x + h t x * qx t x) := by
    intro x hxI
    have ht_eq : ht t x = -((a^2 / (g * A)) * qx t x) :=
      eq_neg_of_add_eq_zero_left (hpde1 t x hxI)
    have qt_eq : qt t x = -((g * A) * hx t x) :=
      eq_neg_of_add_eq_zero_left (hpde2 t x hxI)
    rw [ht_eq, qt_eq]
    field_simp [ha2', hgA, hC2]
    ring
  have hval : (∫ x in (0:ℝ)..L, (g * A / a^2) * (ht t x * h t x + h t x * ht t x) / 2
      + (qt t x * q t x + q t x * qt t x) / (2 * g * A))
      = h t 0 * q t 0 - h t L * q t L := by
    calc (∫ x in (0:ℝ)..L, (g * A / a^2) * (ht t x * h t x + h t x * ht t x) / 2
          + (qt t x * q t x + q t x * qt t x) / (2 * g * A))
        = ∫ x in (0:ℝ)..L, -(hx t x * q t x + h t x * qx t x) := by
          refine intervalIntegral.integral_congr_ae ?_
          refine Filter.Eventually.of_forall (fun x hx => ?_)
          rw [Set.uIoc_of_le h0L] at hx
          exact hkey x (Set.Ioc_subset_Icc_self hx)
      _ = -∫ x in (0:ℝ)..L, (hx t x * q t x + h t x * qx t x) :=
          intervalIntegral.integral_neg
      _ = h t 0 * q t 0 - h t L * q t L := by rw [hFTC]; ring
  rw [hval] at hleib2
  exact hleib2

end FluidDynamics.WaterHammerEnergy
