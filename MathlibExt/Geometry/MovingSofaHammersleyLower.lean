/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Geometry.MovingSofa
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Hammersley's lower bound for the moving sofa

`MovingSofaWanted.hammersley_lower` follows by moving a rectangle with rounded ends and a
semicircular notch through the corridor and integrating the lengths of its vertical sections.
-/

open MeasureTheory Set MovingSofa Real
open scoped ENNReal

namespace MovingSofaWanted

noncomputable section

-- The depth of the lower boundary is measured from the nearest point of the diameter [-a, a].
private def center (a x : ℝ) : ℝ := max (-a) (min a x)
private def cap (x : ℝ) : ℝ := √(1 - x ^ 2)
private def outer (a x : ℝ) : ℝ := cap (x - center a x)
private def notch (a x : ℝ) : ℝ := √(a ^ 2 - x ^ 2)

private def body (a : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc (-a - 1) (a + 1) ∧ -z.im ∈ Icc (notch a z.re) (outer a z.re)}

private theorem cap_le_one (x : ℝ) : cap x ≤ 1 :=
  (Real.sqrt_le_left zero_le_one).2 (by nlinarith [sq_nonneg x])

private theorem notch_le_outer {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) (x : ℝ) :
    notch a x ≤ outer a x := by
  by_cases hx : x ∈ Icc (-a) a
  · rw [outer, center, min_eq_right hx.2, max_eq_right hx.1, sub_self]
    simp only [cap, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_one]
    apply (Real.sqrt_le_left zero_le_one).2
    nlinarith [sq_nonneg x, mul_nonneg ha (sub_nonneg.mpr ha')]
  · have hax : a ≤ |x| := le_of_not_ge (fun h ↦ hx (abs_le.mp h))
    have h : a ^ 2 ≤ x ^ 2 := by simpa using (sq_le_sq₀ ha (abs_nonneg x)).2 hax
    rw [notch, Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr h)]
    exact Real.sqrt_nonneg _

-- Clamping the depth in each vertical section gives a continuous surjection from a rectangle.
private theorem body_regular {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    MeasurableSet (body a) ∧ IsConnected (body a) := by
  let R := Icc (-a - 1) (a + 1) ×ˢ Icc (0 : ℝ) 1
  let f (p : ℝ × ℝ) : ℂ := Complex.equivRealProdCLM.symm
    (p.1, -max (notch a p.1) (min (outer a p.1) p.2))
  have hf : Continuous f := by unfold f; fun_prop [notch, outer, cap, center]
  have heq : f '' R = body a := by
    ext z
    constructor
    · rintro ⟨⟨x, d⟩, ⟨hx, _⟩, rfl⟩
      change x ∈ _ ∧ - -max _ _ ∈ _
      rw [neg_neg]
      exact ⟨hx, le_max_left .., max_le (notch_le_outer ha ha' _) (min_le_left ..)⟩
    · rintro ⟨hx, hl, hu⟩
      refine ⟨(z.re, -z.im), ⟨hx, (Real.sqrt_nonneg _).trans hl, hu.trans (cap_le_one _)⟩, ?_⟩
      apply Complex.ext <;> simp [f, min_eq_right hu, max_eq_right hl]
  rw [← heq]
  exact ⟨((isCompact_Icc.prod isCompact_Icc).image hf).isClosed.measurableSet,
    ((isConnected_Icc (by linarith)).prod (isConnected_Icc zero_le_one)).image _ hf.continuousOn⟩

-- The end caps contribute a unit semicircle. The middle contributes a rectangle
-- of width 2a, from which a semicircle of radius a is removed.
private theorem section_integral {a : ℝ} (ha : 0 < a) :
    (∫ x in (-a - 1)..(a + 1), outer a x - notch a x) =
      π / 2 + 2 * a - a ^ 2 * (π / 2) := by
  let f (x : ℝ) := outer a x - notch a x
  have hf : Continuous f := by unfold f; fun_prop [outer, center, cap, notch]
  have hleft : (∫ x in (-a - 1)..(-a), f x) = ∫ x in (-1 : ℝ)..0, cap x := by
    calc
      _ = ∫ x in (-a - 1)..(-a), cap (x + a) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le (by linarith)]
        intro x hx
        have h := hx.2
        have hsq : a ^ 2 ≤ x ^ 2 := by
          nlinarith [mul_nonneg (by linarith : 0 ≤ -a - x) (by linarith : 0 ≤ a - x)]
        simp [f, outer, center, notch, min_eq_right (by linarith : x ≤ a), max_eq_left h,
          Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr hsq)]
      _ = _ := by rw [intervalIntegral.integral_comp_add_right]; congr 1 <;> ring
  have hright : (∫ x in a..(a + 1), f x) = ∫ x in (0 : ℝ)..1, cap x := by
    calc
      _ = ∫ x in a..(a + 1), cap (x - a) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le (by linarith)]
        intro x hx
        have h := hx.1
        have hsq : a ^ 2 ≤ x ^ 2 := by
          nlinarith [mul_nonneg (by linarith : 0 ≤ x - a) (by linarith : 0 ≤ x + a)]
        simp [f, outer, center, notch, min_eq_left h, max_eq_right (by linarith : -a ≤ a),
          Real.sqrt_eq_zero_of_nonpos (sub_nonpos.mpr hsq)]
      _ = _ := by rw [intervalIntegral.integral_comp_sub_right]; congr 1 <;> ring
  have hmid : (∫ x in (-a)..a, f x) = 2 * a - a ^ 2 * (π / 2) := by
    calc
      _ = ∫ x in (-a)..a, 1 - a * cap (x / a) := by
        apply intervalIntegral.integral_congr
        rw [uIcc_of_le (by linarith)]
        intro x hx
        have heq : a ^ 2 - x ^ 2 = a ^ 2 * (1 - (x / a) ^ 2) := by field_simp
        simp [f, outer, center, notch, min_eq_right hx.2, max_eq_right hx.1, cap, heq,
          Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
      _ = _ := by
        have hg : Continuous fun x ↦ a * cap (x / a) := by fun_prop [cap]
        rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
          (hg.intervalIntegrable _ _), intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_div cap ha.ne']
        simp [ha.ne', cap, integral_sqrt_one_sub_sq]
        ring
  have hc : Continuous cap := by fun_prop [cap]
  have hcaps := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1)
  change (∫ x in (-a - 1)..(a + 1), f x) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable _ (-a)) (hf.intervalIntegrable (-a) _),
    ← intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable (-a) a) (hf.intervalIntegrable a _), hleft, hmid, hright]
  rw [show (∫ x in (-1 : ℝ)..1, cap x) = π / 2 from integral_sqrt_one_sub_sq] at hcaps
  linarith

private theorem area_le_volume_body {a : ℝ} (ha : 0 < a) (ha' : a ≤ 1) :
    ENNReal.ofReal (π / 2 + 2 * a - a ^ 2 * (π / 2)) ≤ volume (body a) := by
  let s := Ioc (-a - 1) (a + 1)
  let lo (x : ℝ) := -outer a x
  let hi (x : ℝ) := -notch a x
  let region := regionBetween lo hi s
  have hlo : Continuous lo := by unfold lo; fun_prop [outer, cap, center]
  have hhi : Continuous hi := by unfold hi; fun_prop [notch]
  have hsub : Complex.measurableEquivRealProd ⁻¹' region ⊆ body a := by
    intro z hz
    obtain ⟨⟨hx, hx'⟩, h₁, h₂⟩ := hz
    change -outer a z.re < z.im at h₁
    change z.im < -notch a z.re at h₂
    exact ⟨⟨hx.le, hx'⟩, by linarith, by linarith⟩
  apply le_trans _ (measure_mono hsub)
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage_equiv]
  change _ ≤ (volume.prod volume) (regionBetween lo hi s)
  rw [volume_regionBetween_eq_integral (hlo.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (hhi.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
    (fun x _ ↦ neg_le_neg (notch_le_outer ha.le ha' x))]
  rw [← section_integral ha, intervalIntegral.integral_of_le (by linarith : -a - 1 ≤ a + 1)]
  simp [lo, hi, sub_eq_add_neg, add_comm]

-- Every coordinate projection of a rotated unit disk has absolute value at most one.
private theorem projection_le_one {u v c s : ℝ} (h : u ^ 2 + v ^ 2 ≤ 1)
    (hcs : c ^ 2 + s ^ 2 = 1) : u * c + v * s ≤ 1 := by
  have hb : (u * c + v * s) ^ 2 ≤ 1 := calc
    _ ≤ (u ^ 2 + v ^ 2) * (c ^ 2 + s ^ 2) := by nlinarith only [sq_nonneg (u * s - v * c)]
    _ ≤ 1 := by rwa [hcs, mul_one]
  exact (le_abs_self _).trans ((sq_le_one_iff_abs_le_one _).mp hb)

private theorem end_disk {a x d : ℝ} (ha : 0 ≤ a) (hx : x ∈ Icc (-a - 1) (a + 1))
    (hd : 0 ≤ d) (hu : d ≤ outer a x) : (x - center a x) ^ 2 + d ^ 2 ≤ 1 := by
  have hoff : |x - center a x| ≤ 1 := by
    obtain ⟨hl, hr⟩ := hx
    rw [abs_le, center]
    rcases le_total x (-a) with h | h
    · rw [min_eq_right (by linarith), max_eq_left h]
      constructor <;> linarith
    · rw [max_eq_right (le_min (by linarith) h)]
      rcases le_total x a with h' | h'
      · simp [min_eq_right h']
      · rw [min_eq_left h']
        constructor <;> linarith
  have hrad := (sq_le_one_iff_abs_le_one _).2 hoff
  have hs := (sq_le_sq₀ hd (Real.sqrt_nonneg _)).2 hu
  rw [Real.sq_sqrt (sub_nonneg.mpr hrad)] at hs
  linarith

-- At angle θ the coordinates relative to the inner corner are
-- ((x - a) cos θ + d sin θ, (x + a) sin θ - d cos θ), with d the depth.
-- The outer walls touch the end disks. A point strictly inside the forbidden quadrant
-- would have x² + d² < a², placing it in the notch.
private theorem turn_fits {a x d c s : ℝ} (ha : 0 ≤ a) (hx : x ∈ Icc (-a - 1) (a + 1))
    (hd : d ∈ Icc (notch a x) (outer a x)) (hc : 0 ≤ c) (hs : 0 ≤ s)
    (hcs : c ^ 2 + s ^ 2 = 1) :
    (x - a) * c + d * s ≤ 1 ∧ 0 ≤ 1 + (x + a) * s - d * c ∧
      ((x + a) * s - d * c ≤ 0 ∨ 0 ≤ (x - a) * c + d * s) := by
  have hd₀ : 0 ≤ d := (Real.sqrt_nonneg _).trans hd.1
  have hb := end_disk ha hx hd₀ hd.2
  have hl : -a ≤ center a x := le_max_left ..
  have hr : center a x ≤ a := max_le (by linarith) (min_le_left ..)
  refine ⟨?_, ?_, ?_⟩
  · linarith only [projection_le_one hb hcs, mul_nonneg (sub_nonneg.mpr hr) hc]
  · have h := projection_le_one (u := -(x - center a x)) (v := d) (c := s) (s := c)
      (by simpa only [neg_sq] using hb) (by linarith)
    linarith only [h, mul_nonneg (by linarith : 0 ≤ center a x + a) hs]
  · by_contra! h
    obtain ⟨hy, hx'⟩ := h
    have h₁ : d * c < (x + a) * s := by linarith
    have h₂ : d * s < (a - x) * c := by linarith
    have hmul := (mul_le_mul_of_nonneg_right h₁.le (mul_nonneg hd₀ hs)).trans_lt
      (mul_lt_mul_of_pos_left h₂ ((mul_nonneg hd₀ hc).trans_lt h₁))
    have hrad := (Real.sqrt_le_left hd₀).mp hd.1
    nlinarith only [hmul, mul_nonneg (sub_nonneg.mpr hrad) (mul_nonneg hs hc)]

-- The first and last thirds of the passage translate the body along the straight arms.
private def phase (t : unitInterval) : ℝ := 3 * (t : ℝ) - 1
private def angle (t : unitInterval) : ℝ := (π / 2) * max 0 (min 1 (phase t))

private def passage (a : ℝ) : Motion where
  rotation := ⟨fun t ↦ Circle.exp (angle t), by fun_prop [angle, phase]⟩
  translation := ⟨fun t ↦ Complex.equivRealProdCLM.symm
    (-a * cos (angle t) + min (phase t) 0, 1 + a * sin (angle t) + max (phase t - 1) 0),
    by fun_prop [angle, phase]⟩

private theorem position_coords (a : ℝ) (t : unitInterval) (z : ℂ) :
    ((passage a).position t z).re =
        (z.re - a) * cos (angle t) + (-z.im) * sin (angle t) + min (phase t) 0 ∧
      ((passage a).position t z).im =
        1 + (z.re + a) * sin (angle t) - (-z.im) * cos (angle t) + max (phase t - 1) 0 := by
  change (((Circle.exp (angle t) : ℂ) * z).re + _ = _) ∧
    (((Circle.exp (angle t) : ℂ) * z).im + _ = _)
  simp only [Circle.coe_exp, Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]
  change _ + (-a * cos (angle t) + min (phase t) 0) = _ ∧
    _ + (1 + a * sin (angle t) + max (phase t - 1) 0) = _
  constructor <;> ring

private theorem body_canPass {a : ℝ} (ha : 0 ≤ a) : CanPass (body a) := by
  have bounds {z : ℂ} (hz : z ∈ body a) :
      (-a - 1 ≤ z.re ∧ z.re ≤ a + 1) ∧ (0 ≤ -z.im ∧ -z.im ≤ 1) :=
    ⟨hz.1, (Real.sqrt_nonneg _).trans hz.2.1, hz.2.2.trans (cap_le_one _)⟩
  refine ⟨passage a, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨⟨_, hr⟩, hl, hu⟩ := bounds hz
    obtain ⟨h₁, h₂⟩ := position_coords a 0 z
    norm_num [angle, phase] at h₁ h₂
    change _ ≤ 0 ∧ 0 ≤ _ ∧ _ ≤ 1
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨⟨hx, _⟩, hl, hu⟩ := bounds hz
    obtain ⟨h₁, h₂⟩ := position_coords a 1 z
    norm_num [angle, phase] at h₁ h₂
    change 0 ≤ _ ∧ _ ≤ 1 ∧ 1 ≤ _
    exact ⟨by linarith, by linarith, by linarith⟩
  · intro t
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨⟨hl, hr⟩, hd, hd'⟩ := bounds hz
    obtain ⟨h₁, h₂⟩ := position_coords a t z
    change (_ ≤ 1 ∧ 0 ≤ _ ∧ _ ≤ 1) ∨ (0 ≤ _ ∧ _ ≤ 1 ∧ 0 ≤ _)
    rw [h₁, h₂]
    rcases le_or_gt (phase t) 0 with h | h
    · have hθ : angle t = 0 := by simp [angle, max_eq_left ((min_le_right ..).trans h)]
      simp only [hθ, cos_zero, sin_zero, mul_one, mul_zero, add_zero,
        min_eq_left h, max_eq_right (by linarith : phase t - 1 ≤ 0)]
      exact Or.inl ⟨by linarith, by linarith, by linarith⟩
    rcases le_or_gt 1 (phase t) with h' | h'
    · have hθ : angle t = π / 2 := by simp [angle, min_eq_left h']
      simp only [hθ, cos_pi_div_two, sin_pi_div_two, mul_one, mul_zero, add_zero, zero_add,
        sub_zero, min_eq_right h.le, max_eq_left (sub_nonneg.mpr h')]
      exact Or.inr ⟨by linarith, by linarith, by linarith⟩
    · have hθ : angle t = π / 2 * phase t := by simp [angle, min_eq_right h'.le, max_eq_right h.le]
      have hθ₀ : 0 ≤ angle t := hθ ▸ mul_nonneg pi_div_two_pos.le h.le
      have hθ₁ : angle t ≤ π / 2 := by
        rw [hθ]
        exact mul_le_of_le_one_right pi_div_two_pos.le h'.le
      obtain ⟨hx, hy, hh⟩ := turn_fits ha hz.1 hz.2
        (cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], hθ₁⟩)
        (sin_nonneg_of_nonneg_of_le_pi hθ₀ (by linarith [pi_pos]))
        (cos_sq_add_sin_sq _)
      rw [min_eq_right h.le, max_eq_right (sub_nonpos.mpr h'.le), add_zero, add_zero]
      rcases hh with hh | hh
      · exact Or.inl ⟨hx, hy, by linarith⟩
      · exact Or.inr ⟨hh, hx, hy⟩

/-- **Hammersley's lower bound for the moving sofa constant.** The moving sofa constant, the
supremum of the areas of connected Lebesgue-measurable planar shapes that a continuous rigid motion
can carry through the right-angled corridor of width $1$, is at least $\pi/2 + 2/\pi$.

Source: catalogue line 21, Hammersley (1968). Construction not retained. -/
public theorem hammersley_lower :
    ENNReal.ofReal (Real.pi / 2 + 2 / Real.pi) ≤ MovingSofa.optimalArea := by
  let a := 2 / π
  have ha : 0 < a := div_pos zero_lt_two pi_pos
  have ha' : a ≤ 1 := (div_le_one pi_pos).2 Real.two_le_pi
  obtain ⟨hm, hc⟩ := body_regular ha.le ha'
  have hsofa : IsSofa (body a) := ⟨hm.nullMeasurableSet, hc, body_canPass ha.le⟩
  have harea := area_le_volume_body ha ha'
  have heq : π / 2 + 2 * a - a ^ 2 * (π / 2) = π / 2 + 2 / π := by
    unfold a
    field_simp
    ring
  rw [heq] at harea
  exact harea.trans (le_iSup_of_le (body a) (le_iSup_of_le hsofa le_rfl))

end

end MovingSofaWanted
