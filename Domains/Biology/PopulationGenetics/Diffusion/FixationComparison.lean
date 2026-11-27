/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Diffusion.GeneralDiffusion
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Order.Monotone.Defs

open Set

/-!
# Fixation comparison with neutrality

Target module: `Domains.Biology.PopulationGenetics.Diffusion.FixationComparison`.

This module compares the analytic fixation ratio `S p / S 1` of a regular
diffusion on `(0, 1)` with the neutral diagonal `p`, according to the sign of
the drift-to-variance ratio `b / a` at fixed variance `a`.

The scale density `ψ` satisfies `ψ' x = -(2 * b x / a x) * ψ x` on `(0, 1)`
with `ψ > 0`. A nonnegative ratio makes `ψ` antitone, hence the scale function
`S` concave, so the Dirichlet ratio lies on or above the diagonal; a
nonpositive ratio reverses the comparison. Neutrality (`b = 0`) gives `ψ = 1`
and ratio `p` for every variance function `a`, so this is a genuine comparison
with neutrality at fixed `a`. For frequency-dependent selection with
Wright-Fisher variance, the sign of `b / a` is the sign of the local selection
pressure.

`fixationProb` is the analytic Dirichlet ratio `S p / S 1`. It is a hitting
probability only under Feller boundary accessibility, which regular diffusion
does not imply, so no process-level claim is made here. Only weak inequalities
are stated.

References: Karlin and Taylor (1981), Chapter 15; Ewens (2004), Chapter 4.
-/

@[expose] public section
namespace MathlibExt.Biology.PopulationGenetics.Diffusion

/-- Scale density is antitone when the drift-to-variance ratio is nonnegative.

Mathematics: `ψ' x = -(2 * b x / a x) * ψ x` on `(0, 1)` with `ψ > 0`, so a
nonnegative pointwise ratio gives a nonpositive derivative and `ψ` is antitone
on the closed interval by continuity.
Conventions: `b / a` is the pointwise drift-to-variance ratio and `h` is the
regular-diffusion hypothesis on `(0, 1)`.
Not claimed: strict antitonicity, or any process-level hitting probability.
See Karlin and Taylor (1981), Chapter 15, and Ewens (2004), Chapter 4. -/
theorem scaleDensity_antitoneOn_of_nonneg (b a : ℝ → ℝ)
    (h : IsRegularDiffusion b a)
    (hdrift : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ b x / a x) :
    AntitoneOn (scaleDensity b a) (Icc 0 1) := by
  have hI : interior (Icc (0 : ℝ) 1) = Ioo 0 1 := interior_Icc
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    h.continuousOn_scaleDensity
    (f' := fun x => -(2 * b x / a x) * scaleDensity b a x) ?_ ?_
  · intro x hx
    rw [hI] at hx
    exact (h.hasDerivAt_scaleDensity hx).hasDerivWithinAt
  · intro x hx
    rw [hI] at hx
    have hr : 0 ≤ 2 * b x / a x := by
      rw [mul_div_assoc]
      exact mul_nonneg (by norm_num) (hdrift x hx)
    have hψ : 0 ≤ scaleDensity b a x := (scaleDensity_pos b a x).le
    have hnn : 0 ≤ (2 * b x / a x) * scaleDensity b a x :=
      mul_nonneg hr hψ
    calc -(2 * b x / a x) * scaleDensity b a x
        = -((2 * b x / a x) * scaleDensity b a x) := neg_mul _ _
      _ ≤ 0 := neg_nonpos.mpr hnn

/-- Scale density is monotone when the drift-to-variance ratio is nonpositive.

Mathematics: `ψ' x = -(2 * b x / a x) * ψ x` on `(0, 1)` with `ψ > 0`, so a
nonpositive pointwise ratio gives a nonnegative derivative and `ψ` is monotone
on the closed interval by continuity.
Conventions: `b / a` is the pointwise drift-to-variance ratio and `h` is the
regular-diffusion hypothesis on `(0, 1)`.
Not claimed: strict monotonicity, or any process-level hitting probability.
See Karlin and Taylor (1981), Chapter 15, and Ewens (2004), Chapter 4. -/
theorem scaleDensity_monotoneOn_of_nonpos (b a : ℝ → ℝ)
    (h : IsRegularDiffusion b a)
    (hdrift : ∀ x ∈ Ioo (0 : ℝ) 1, b x / a x ≤ 0) :
    MonotoneOn (scaleDensity b a) (Icc 0 1) := by
  have hI : interior (Icc (0 : ℝ) 1) = Ioo 0 1 := interior_Icc
  refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    h.continuousOn_scaleDensity
    (f' := fun x => -(2 * b x / a x) * scaleDensity b a x) ?_ ?_
  · intro x hx
    rw [hI] at hx
    exact (h.hasDerivAt_scaleDensity hx).hasDerivWithinAt
  · intro x hx
    rw [hI] at hx
    have hr : 2 * b x / a x ≤ 0 := by
      rw [mul_div_assoc]
      exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hdrift x hx)
    have hψ : 0 ≤ scaleDensity b a x := (scaleDensity_pos b a x).le
    have hnp : (2 * b x / a x) * scaleDensity b a x ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hr hψ
    calc 0 ≤ -((2 * b x / a x) * scaleDensity b a x) :=
          neg_nonneg.mpr hnp
      _ = -(2 * b x / a x) * scaleDensity b a x := (neg_mul _ _).symm

/-- The analytic fixation ratio lies on or above the neutral diagonal when the
drift-to-variance ratio is nonnegative.

Mathematics: an antitone scale density makes the scale function `S` concave
with `S 0 = 0`, so the Dirichlet ratio `S p / S 1` dominates `p` on `[0, 1]`.
Conventions: comparison with neutrality at fixed variance `a`; neutral drift
`b = 0` gives ratio exactly `p`.
Not claimed: strict inequality, or any process-level hitting probability
(which needs Feller boundary accessibility).
See Karlin and Taylor (1981), Chapter 15, and Ewens (2004), Chapter 4. -/
theorem le_fixationProb_of_nonneg (b a : ℝ → ℝ) (p : ℝ)
    (h : IsRegularDiffusion b a)
    (hdrift : ∀ x ∈ Ioo (0 : ℝ) 1, 0 ≤ b x / a x)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    p ≤ fixationProb b a p := by
  have hanti := scaleDensity_antitoneOn_of_nonneg b a h hdrift
  have hS1 : 0 < scaleFunction b a 1 := h.scaleFunction_one_pos
  rcases eq_or_lt_of_le hp.1 with rfl | h0p
  · simp
  rcases eq_or_lt_of_le hp.2 with rfl | hp1
  · simp [h.fixationProb_one]
  have hcont := h.continuousOn_scaleDensity
  have hint0p : IntervalIntegrable (scaleDensity b a) MeasureTheory.volume 0 p :=
    (hcont.mono (Icc_subset_Icc_right hp.2)).intervalIntegrable_of_Icc hp.1
  have hintp1 : IntervalIntegrable (scaleDensity b a) MeasureTheory.volume p 1 :=
    (hcont.mono (Icc_subset_Icc_left hp.1)).intervalIntegrable_of_Icc hp1.le
  have hle : ∀ x ∈ Icc (0 : ℝ) p, scaleDensity b a p ≤ scaleDensity b a x :=
    fun x hx => hanti ⟨hx.1, hx.2.trans hp.2⟩ hp hx.2
  have hge : ∀ x ∈ Icc p 1, scaleDensity b a x ≤ scaleDensity b a p := by
    intro x hx
    exact hanti hp ⟨hp.1.trans hx.1, hx.2⟩ hx.1
  have hlow : p * scaleDensity b a p ≤ scaleFunction b a p := by
    have hc : IntervalIntegrable (fun _ => scaleDensity b a p)
        MeasureTheory.volume 0 p :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on h0p.le hc hint0p hle
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hmono
    exact hmono
  have hhigh :
      ∫ y in p..1, scaleDensity b a y ≤ (1 - p) * scaleDensity b a p := by
    have hc : IntervalIntegrable (fun _ => scaleDensity b a p)
        MeasureTheory.volume p 1 :=
      intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hp1.le hintp1 hc hge
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hmono
    exact hmono
  have hsplit : scaleFunction b a p + ∫ y in p..1, scaleDensity b a y
      = scaleFunction b a 1 :=
    intervalIntegral.integral_add_adjacent_intervals hint0p hintp1
  show p ≤ scaleFunction b a p / scaleFunction b a 1
  rw [le_div_iff₀ hS1]
  have h1p : 0 ≤ 1 - p := by linarith [hp.2]
  have step1 : p * (∫ y in p..1, scaleDensity b a y)
      ≤ p * ((1 - p) * scaleDensity b a p) :=
    mul_le_mul_of_nonneg_left hhigh hp.1
  have step2 : (1 - p) * (p * scaleDensity b a p)
      ≤ (1 - p) * scaleFunction b a p :=
    mul_le_mul_of_nonneg_left hlow h1p
  have key : p * (∫ y in p..1, scaleDensity b a y)
      ≤ (1 - p) * scaleFunction b a p := by
    calc p * (∫ y in p..1, scaleDensity b a y)
        ≤ p * ((1 - p) * scaleDensity b a p) := step1
      _ = (1 - p) * (p * scaleDensity b a p) := by ring
      _ ≤ (1 - p) * scaleFunction b a p := step2
  have hsplit' : p * scaleFunction b a 1
      = p * scaleFunction b a p + p * (∫ y in p..1, scaleDensity b a y) := by
    rw [← hsplit]; ring
  rw [hsplit']
  calc p * scaleFunction b a p + p * (∫ y in p..1, scaleDensity b a y)
      ≤ p * scaleFunction b a p + (1 - p) * scaleFunction b a p :=
        add_le_add_right key _
    _ = scaleFunction b a p := by ring

/-- The analytic fixation ratio lies on or below the neutral diagonal when the
drift-to-variance ratio is nonpositive.

Mathematics: a monotone scale density makes the scale function `S` convex with
`S 0 = 0`, so the Dirichlet ratio `S p / S 1` is dominated by `p` on `[0, 1]`.
Conventions: comparison with neutrality at fixed variance `a`; neutral drift
`b = 0` gives ratio exactly `p`.
Not claimed: strict inequality, or any process-level hitting probability
(which needs Feller boundary accessibility).
See Karlin and Taylor (1981), Chapter 15, and Ewens (2004), Chapter 4. -/
theorem fixationProb_le_of_nonpos (b a : ℝ → ℝ) (p : ℝ)
    (h : IsRegularDiffusion b a)
    (hdrift : ∀ x ∈ Ioo (0 : ℝ) 1, b x / a x ≤ 0)
    (hp : p ∈ Icc (0 : ℝ) 1) :
    fixationProb b a p ≤ p := by
  have hmono := scaleDensity_monotoneOn_of_nonpos b a h hdrift
  have hS1 : 0 < scaleFunction b a 1 := h.scaleFunction_one_pos
  rcases eq_or_lt_of_le hp.1 with rfl | h0p
  · simp
  rcases eq_or_lt_of_le hp.2 with rfl | hp1
  · simp [h.fixationProb_one]
  have hcont := h.continuousOn_scaleDensity
  have hint0p : IntervalIntegrable (scaleDensity b a) MeasureTheory.volume 0 p :=
    (hcont.mono (Icc_subset_Icc_right hp.2)).intervalIntegrable_of_Icc hp.1
  have hintp1 : IntervalIntegrable (scaleDensity b a) MeasureTheory.volume p 1 :=
    (hcont.mono (Icc_subset_Icc_left hp.1)).intervalIntegrable_of_Icc hp1.le
  have hle : ∀ x ∈ Icc (0 : ℝ) p, scaleDensity b a x ≤ scaleDensity b a p :=
    fun x hx => hmono ⟨hx.1, hx.2.trans hp.2⟩ hp hx.2
  have hge : ∀ x ∈ Icc p 1, scaleDensity b a p ≤ scaleDensity b a x := by
    intro x hx
    exact hmono hp ⟨hp.1.trans hx.1, hx.2⟩ hx.1
  have hlow : scaleFunction b a p ≤ p * scaleDensity b a p := by
    have hc : IntervalIntegrable (fun _ => scaleDensity b a p)
        MeasureTheory.volume 0 p :=
      intervalIntegrable_const
    have hint := intervalIntegral.integral_mono_on h0p.le hint0p hc hle
    simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
    exact hint
  have hhigh :
      (1 - p) * scaleDensity b a p ≤ ∫ y in p..1, scaleDensity b a y := by
    have hc : IntervalIntegrable (fun _ => scaleDensity b a p)
        MeasureTheory.volume p 1 :=
      intervalIntegrable_const
    have hint := intervalIntegral.integral_mono_on hp1.le hc hintp1 hge
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hint
    exact hint
  have hsplit : scaleFunction b a p + ∫ y in p..1, scaleDensity b a y
      = scaleFunction b a 1 :=
    intervalIntegral.integral_add_adjacent_intervals hint0p hintp1
  show scaleFunction b a p / scaleFunction b a 1 ≤ p
  rw [div_le_iff₀ hS1]
  have h1p : 0 ≤ 1 - p := by linarith [hp.2]
  have step1 : (1 - p) * scaleFunction b a p
      ≤ (1 - p) * (p * scaleDensity b a p) :=
    mul_le_mul_of_nonneg_left hlow h1p
  have step2 : p * ((1 - p) * scaleDensity b a p)
      ≤ p * (∫ y in p..1, scaleDensity b a y) :=
    mul_le_mul_of_nonneg_left hhigh hp.1
  have key : (1 - p) * scaleFunction b a p
      ≤ p * (∫ y in p..1, scaleDensity b a y) := by
    calc (1 - p) * scaleFunction b a p
        ≤ (1 - p) * (p * scaleDensity b a p) := step1
      _ = p * ((1 - p) * scaleDensity b a p) := by ring
      _ ≤ p * (∫ y in p..1, scaleDensity b a y) := step2
  have hsplit' : p * scaleFunction b a 1
      = p * scaleFunction b a p + p * (∫ y in p..1, scaleDensity b a y) := by
    rw [← hsplit]; ring
  rw [hsplit']
  calc scaleFunction b a p
      = p * scaleFunction b a p + (1 - p) * scaleFunction b a p := by ring
    _ ≤ p * scaleFunction b a p + p * (∫ y in p..1, scaleDensity b a y) :=
        add_le_add_right key _

end MathlibExt.Biology.PopulationGenetics.Diffusion
