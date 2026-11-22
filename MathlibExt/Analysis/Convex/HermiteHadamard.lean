/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Separation.CompletelyRegular

namespace MetaMathlibExt

@[expose] public section

/-- **Hermite–Hadamard inequality.** Let $a < b$ be real numbers and let
$f \colon \mathbb{R} \to \mathbb{R}$ be convex on $[a, b]$. Then
$f\left(\frac{a+b}{2}\right) \le \frac{1}{b-a} \int_a^b f(x)\,dx$ and
$\frac{1}{b-a} \int_a^b f(x)\,dx \le \frac{f(a) + f(b)}{2}$.

Source: `https://en.wikipedia.org/wiki/Hermite%E2%80%93Hadamard_inequality`, statement
`hermite-hadamard-s1`; proves `Wanted` entry `hermite_hadamard`.
-/
theorem hermite_hadamard {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ConvexOn ℝ (Set.Icc a b) f) :
    f ((a + b) / 2) ≤ (1 / (b - a)) * ∫ x in a..b, f x ∧
    (1 / (b - a)) * ∫ x in a..b, f x ≤ (f a + f b) / 2 := by
  have hab' : a ≤ b := le_of_lt hab
  have hba : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hbane : b - a ≠ 0 := ne_of_gt hba
  have ha_mem : a ∈ Set.Icc a b := ⟨le_refl a, hab'⟩
  have hb_mem : b ∈ Set.Icc a b := ⟨hab', le_refl b⟩
  -- Secant upper bound from convexity.
  have hub : ∀ x ∈ Set.Icc a b,
      f x ≤ ((b - x) * f a + (x - a) * f b) / (b - a) := by
    intro x hx
    have h1 : (0 : ℝ) ≤ (b - x) / (b - a) :=
      div_nonneg (sub_nonneg.mpr hx.2) hba.le
    have h2 : (0 : ℝ) ≤ (x - a) / (b - a) :=
      div_nonneg (sub_nonneg.mpr hx.1) hba.le
    have h3 : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
      rw [← add_div, div_eq_iff hbane]
      ring
    have hcomb : ((b - x) / (b - a)) • a + ((x - a) / (b - a)) • b = x := by
      simp only [smul_eq_mul]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hbane]
      ring
    have h := hf.2 ha_mem hb_mem h1 h2 h3
    rw [hcomb] at h
    simp only [smul_eq_mul] at h
    calc f x ≤ (b - x) / (b - a) * f a + (x - a) / (b - a) * f b := h
      _ = ((b - x) * f a + (x - a) * f b) / (b - a) := by ring
  -- Reflection stays in the interval.
  have hrefl_mem : ∀ x ∈ Set.Icc a b, a + b - x ∈ Set.Icc a b := by
    intro x hx
    exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
  -- Midpoint convexity bound.
  have hmid : ∀ x ∈ Set.Icc a b,
      f ((a + b) / 2) ≤ (f x + f (a + b - x)) / 2 := by
    intro x hx
    have hx' := hrefl_mem x hx
    have h := hf.2 hx hx' (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
    have hcomb : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (a + b - x) = (a + b) / 2 := by
      simp only [smul_eq_mul]
      ring
    rw [hcomb] at h
    simp only [smul_eq_mul] at h
    linarith
  -- Upper bound by endpoint values.
  have hU : ∀ x ∈ Set.Icc a b, f x ≤ |f a| + |f b| := by
    intro x hx
    have h1 : (0 : ℝ) ≤ (b - x) / (b - a) :=
      div_nonneg (sub_nonneg.mpr hx.2) hba.le
    have h2 : (0 : ℝ) ≤ (x - a) / (b - a) :=
      div_nonneg (sub_nonneg.mpr hx.1) hba.le
    have h3 : (b - x) / (b - a) + (x - a) / (b - a) = 1 := by
      rw [← add_div, div_eq_iff hbane]
      ring
    have hle : f x ≤ (b - x) / (b - a) * f a + (x - a) / (b - a) * f b := by
      have h := hub x hx
      have heq : ((b - x) * f a + (x - a) * f b) / (b - a)
          = (b - x) / (b - a) * f a + (x - a) / (b - a) * f b := by ring
      rwa [heq] at h
    calc f x ≤ (b - x) / (b - a) * f a + (x - a) / (b - a) * f b := hle
      _ ≤ (b - x) / (b - a) * (|f a| + |f b|)
          + (x - a) / (b - a) * (|f a| + |f b|) := by
        apply add_le_add
        · exact le_trans (mul_le_mul_of_nonneg_left (le_abs_self (f a)) h1)
            (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_right (abs_nonneg (f b))) h1)
        · exact le_trans (mul_le_mul_of_nonneg_left (le_abs_self (f b)) h2)
            (mul_le_mul_of_nonneg_left
              (le_add_of_nonneg_left (abs_nonneg (f a))) h2)
      _ = |f a| + |f b| := by rw [← add_mul, h3, one_mul]
  -- Lower bound via the midpoint value.
  have hL : ∀ x ∈ Set.Icc a b,
      -(|f a| + |f b| + 2 * |f ((a + b) / 2)|) ≤ f x := by
    intro x hx
    have h1 := hmid x hx
    have h2 := hU (a + b - x) (hrefl_mem x hx)
    have h3 : -(f ((a + b) / 2)) ≤ |f ((a + b) / 2)| := neg_le_abs _
    linarith
  -- Combined norm bound.
  have hC : ∀ x ∈ Set.Icc a b,
      ‖f x‖ ≤ |f a| + |f b| + 2 * |f ((a + b) / 2)| := by
    intro x hx
    rw [Real.norm_eq_abs, abs_le]
    refine ⟨hL x hx, ?_⟩
    calc f x ≤ |f a| + |f b| := hU x hx
      _ ≤ |f a| + |f b| + 2 * |f ((a + b) / 2)| := by
        linarith [abs_nonneg (f ((a + b) / 2))]
  -- Convex implies continuous on the open interval.
  have hcont : ContinuousOn f (Set.Ioo a b) := by
    have h := hf.continuousOn_interior
    rwa [interior_Icc] at h
  have hmeas : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Set.Ioo a b)) :=
    hcont.aestronglyMeasurable measurableSet_Ioo
  -- Bounded + measurable on a finite-measure set gives integrability.
  have hInt_Ioo : MeasureTheory.IntegrableOn f (Set.Ioo a b) MeasureTheory.volume := by
    have hfin : MeasureTheory.volume (Set.Ioo a b) < ⊤ := by
      rw [Real.volume_Ioo]
      exact ENNReal.ofReal_lt_top
    have hbdd : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioo a b)),
        ‖f x‖ ≤ |f a| + |f b| + 2 * |f ((a + b) / 2)| := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx
      exact hC x ⟨hx.1.le, hx.2.le⟩
    exact MeasureTheory.IntegrableOn.of_bound hfin hmeas _ hbdd
  -- Endpoints are null sets, so this extends to the closed interval.
  have hInt : IntervalIntegrable f MeasureTheory.volume a b := by
    have hIcc : MeasureTheory.IntegrableOn f (Set.Icc a b) MeasureTheory.volume :=
      (integrableOn_Icc_iff_integrableOn_Ioo).mpr hInt_Ioo
    exact (intervalIntegrable_iff_integrableOn_Icc_of_le hab').mpr hIcc
  -- Secant bound in affine form.
  have hub_aff : ∀ x ∈ Set.Icc a b,
      f x ≤ (f b - f a) / (b - a) * x + (b * f a - a * f b) / (b - a) := by
    intro x hx
    have h := hub x hx
    have heq : ((b - x) * f a + (x - a) * f b) / (b - a)
        = (f b - f a) / (b - a) * x + (b * f a - a * f b) / (b - a) := by ring
    rwa [heq] at h
  have hbase : IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume a b :=
    Continuous.intervalIntegrable continuous_id' a b
  have hg1 := hbase.const_mul ((f b - f a) / (b - a))
  have hg2 : IntervalIntegrable (fun _ : ℝ => (b * f a - a * f b) / (b - a))
      MeasureTheory.volume a b :=
    intervalIntegrable_const
  have hgInt_aff : IntervalIntegrable
      (fun x : ℝ => (f b - f a) / (b - a) * x + (b * f a - a * f b) / (b - a))
      MeasureTheory.volume a b :=
    hg1.add hg2
  have hadd : (∫ x in a..b, ((f b - f a) / (b - a) * x + (b * f a - a * f b) / (b - a)))
      = (∫ x in a..b, (f b - f a) / (b - a) * x)
        + ∫ _ in a..b, (b * f a - a * f b) / (b - a) :=
    intervalIntegral.integral_add hg1 hg2
  -- The secant majorant integrates to the trapezoidal value.
  have hg_eq : (∫ x in a..b, ((f b - f a) / (b - a) * x + (b * f a - a * f b) / (b - a)))
      = (b - a) * (f a + f b) / 2 := by
    rw [hadd, intervalIntegral.integral_const_mul, integral_id,
      intervalIntegral.integral_const]
    simp only [smul_eq_mul]
    field_simp
    ring
  -- Right-hand inequality.
  have hRight : (1 / (b - a)) * ∫ x in a..b, f x ≤ (f a + f b) / 2 := by
    have hle : (∫ x in a..b, f x)
        ≤ ∫ x in a..b, ((f b - f a) / (b - a) * x + (b * f a - a * f b) / (b - a)) :=
      intervalIntegral.integral_mono_on hab' hInt hgInt_aff hub_aff
    rw [hg_eq] at hle
    have hpos : (0 : ℝ) < 1 / (b - a) := one_div_pos.mpr hba
    calc (1 / (b - a)) * ∫ x in a..b, f x
        ≤ (1 / (b - a)) * ((b - a) * (f a + f b) / 2) :=
          mul_le_mul_of_nonneg_left hle hpos.le
      _ = (f a + f b) / 2 := by
        rw [one_div, ← mul_div_assoc, inv_mul_cancel_left₀ hbane]
  -- Reflection of an integrable function is integrable.
  have hInt_refl : IntervalIntegrable (fun x => f (a + b - x)) MeasureTheory.volume a b := by
    have hneg : IntervalIntegrable (fun y => f (-y)) MeasureTheory.volume (-a) (-b) :=
      (IntervalIntegrable.iff_comp_neg).mp hInt
    have hsub := hneg.comp_sub_right (a + b)
    rw [show (-a + (a + b)) = b by ring, show (-b + (a + b)) = a by ring] at hsub
    have heq : (fun x : ℝ => (fun y => f (-y)) (x - (a + b)))
        = (fun x => f (a + b - x)) := by
      funext x
      show f (-(x - (a + b))) = f (a + b - x)
      congr 1
      ring
    rw [heq] at hsub
    exact hsub.symm
  -- Reflection preserves the interval integral.
  have hrefl_eq : (∫ x in a..b, f (a + b - x)) = ∫ x in a..b, f x := by
    have h : (∫ x in a..b, f ((a + b) - x))
        = ∫ x in (a + b) - b..(a + b) - a, f x :=
      intervalIntegral.integral_comp_sub_left f (a + b)
    rwa [show (a + b) - b = a by ring, show (a + b) - a = b by ring] at h
  have hlow : ∀ x ∈ Set.Icc a b,
      2 * f ((a + b) / 2) - f (a + b - x) ≤ f x := by
    intro x hx
    have h := hmid x hx
    linarith
  have hInt_low : IntervalIntegrable
      (fun x => 2 * f ((a + b) / 2) - f (a + b - x)) MeasureTheory.volume a b :=
    intervalIntegrable_const.sub hInt_refl
  have hsub : (∫ x in a..b, (2 * f ((a + b) / 2) - f (a + b - x)))
      = (∫ _ in a..b, 2 * f ((a + b) / 2)) - ∫ x in a..b, f (a + b - x) :=
    intervalIntegral.integral_sub intervalIntegrable_const hInt_refl
  have hLHS : (∫ x in a..b, (2 * f ((a + b) / 2) - f (a + b - x)))
      = 2 * ((b - a) * f ((a + b) / 2)) - ∫ x in a..b, f x := by
    rw [hsub, intervalIntegral.integral_const, hrefl_eq]
    simp only [smul_eq_mul]
    ring
  -- Left-hand inequality.
  have hLeft : f ((a + b) / 2) ≤ (1 / (b - a)) * ∫ x in a..b, f x := by
    have hle2 : (∫ x in a..b, (2 * f ((a + b) / 2) - f (a + b - x)))
        ≤ ∫ x in a..b, f x :=
      intervalIntegral.integral_mono_on hab' hInt_low hInt hlow
    have h2 : (b - a) * f ((a + b) / 2) ≤ ∫ x in a..b, f x := by
      linarith [hle2, hLHS]
    have hpos : (0 : ℝ) < 1 / (b - a) := one_div_pos.mpr hba
    calc f ((a + b) / 2) = (1 / (b - a)) * ((b - a) * f ((a + b) / 2)) := by
            rw [one_div, inv_mul_cancel_left₀ hbane]
      _ ≤ (1 / (b - a)) * ∫ x in a..b, f x :=
            mul_le_mul_of_nonneg_left h2 hpos.le
  exact ⟨hLeft, hRight⟩

end

end MetaMathlibExt
