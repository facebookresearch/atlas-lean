/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Contact and lubrication

Reduced models of contact and lubrication. Section A solves the one-dimensional Reynolds equation
for a plane slider with a linear converging film in closed form; the pressure and the load per
unit width are positive for the converging orientation.

## i. Overview

Section A treats plane-slider lubrication.

A plane slider of length `L > 0` carries an incompressible isoviscous lubricant of viscosity
`μ > 0` in the film `h x = h0 + (hL - h0) x / L` between the inlet `x = 0` and the outlet
`x = L`. The lower surface slides with speed `U > 0` in the direction of increasing `x`. The
stated reduced model is the Reynolds equation `(h³ p')' = 6 μ U h'` on `[0, L]` with ambient
pressure `p 0 = p L = 0` at both ends and no cavitation; it is a model input, not a proved thin
film limit of the Navier-Stokes equations. Here the model is the predicate
`IsReynoldsSolution`: `p` has derivative `p'` on `[0, L]` and the flux `h³ p'` has derivative
`6 μ U (hL - h0) / L` there.

For positive end thicknesses `h0 ≠ hL` the model has exactly one solution,
`p = 6 μ U L (h0 - h) (h - hL) / ((h0² - hL²) h²)`, with gradient
`p' = 6 μ U (h - h_m) / h³` and `h_m = 2 h0 hL / (h0 + hL)`. Its load per unit width is
`W = ∫₀ᴸ p = 6 μ U L² / (h0 - hL)² (log (h0 / hL) - 2 (h0 - hL) / (h0 + hL))`. For the
converging film `h0 > hL > 0` the pressure is positive inside the slider and `W > 0`. For a
diverging film `0 < h0 < hL` the same formula is negative inside the slider: the gauge pressure
falls below ambient, where a real film cavitates, so the no-cavitation model is not valid there.
A film that closes at the outlet, `hL = 0`, admits no solution at all.

Cavitation models, side leakage, thermal and elastic effects and the derivation of the Reynolds
equation are not treated.

## ii. Key results

- `Elasticity.ContactAndLubrication.sliderPressure_isReynoldsSolution`: the closed-form
  pressure solves the model.
- `Elasticity.ContactAndLubrication.isReynoldsSolution_unique`: every solution is the closed-form
  pressure.
- `Elasticity.ContactAndLubrication.sliderPressure_pos`: the pressure is positive for a converging
  film.
- `Elasticity.ContactAndLubrication.sliderLoad_eq`: the load per unit width in closed form.
- `Elasticity.ContactAndLubrication.sliderLoad_pos`: the load is positive for a converging film.
- `Elasticity.ContactAndLubrication.sliderPressure_neg_of_diverging`: a diverging film gives
  negative pressure.
- `Elasticity.ContactAndLubrication.not_isReynoldsSolution_of_hL_eq_zero`: an outlet thickness
  `hL = 0` is rejected.

## iii. Table of contents

- A. Plane-slider lubrication
  - A.1. Film, model and closed-form pressure
  - A.2. Solution of the Reynolds model
  - A.3. Positivity and load for the converging film
  - A.4. Diverging and closed films

## iv. References

- O. Reynolds, On the theory of lubrication and its application to Mr. Beauchamp Tower's
  experiments, *Philosophical Transactions of the Royal Society of London* 177 (1886).
- B. J. Hamrock, S. R. Schmid and B. O. Jacobson, *Fundamentals of Fluid Film Lubrication*,
  2nd ed., Marcel Dekker (2004): the Reynolds equation and the fixed-incline slider bearing.
-/

@[expose] public section

namespace Elasticity.ContactAndLubrication

/-! ## A. Plane-slider lubrication -/

/-! ### A.1. Film, model and closed-form pressure -/

/-- Linear film thickness of the plane slider: `h0` at the inlet `x = 0` and `hL` at the
outlet `x = L`. -/
noncomputable def sliderFilm (h0 hL L x : ℝ) : ℝ :=
  h0 + (hL - h0) * x / L

/-- The stated Reynolds model on `[0, L]`: the pressure `p` has derivative `p'`, the flux
`h³ p'` has derivative `6 μ U h'` with the film slope `h' = (hL - h0) / L`, and `p` vanishes at
both ends. -/
def IsReynoldsSolution (μ U h0 hL L : ℝ) (p p' : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc 0 L, HasDerivAt p (p' x) x) ∧
    (∀ x ∈ Set.Icc 0 L,
      HasDerivAt (fun y => sliderFilm h0 hL L y ^ 3 * p' y) (6 * μ * U * ((hL - h0) / L)) x) ∧
    p 0 = 0 ∧ p L = 0

/-- Closed-form plane-slider pressure `6 μ U L (h0 - h) (h - hL) / ((h0² - hL²) h²)` with
`h = sliderFilm h0 hL L x`. -/
noncomputable def sliderPressure (μ U h0 hL L x : ℝ) : ℝ :=
  6 * μ * U * L * (h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL) /
    ((h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L x ^ 2)

/-- Plane-slider pressure gradient `6 μ U (h - 2 h0 hL / (h0 + hL)) / h³` with
`h = sliderFilm h0 hL L x`. -/
noncomputable def sliderPressureGradient (μ U h0 hL L x : ℝ) : ℝ :=
  6 * μ * U * (sliderFilm h0 hL L x - 2 * h0 * hL / (h0 + hL)) / sliderFilm h0 hL L x ^ 3

/-- Load per unit width: the integral of the slider pressure over `[0, L]`. -/
noncomputable def sliderLoad (μ U h0 hL L : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, sliderPressure μ U h0 hL L x

/-- The film stays open: for positive end thicknesses the film is positive on `[0, L]`. -/
lemma sliderFilm_pos {h0 hL L x : ℝ} (h0pos : 0 < h0) (hLpos : 0 < hL) (hL0 : 0 < L)
    (hx : x ∈ Set.Icc 0 L) :
    0 < sliderFilm h0 hL L x := by
  unfold sliderFilm
  obtain ⟨hx0, hxL⟩ := hx
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hnum : 0 < h0 * L + (hL - h0) * x := by
    by_cases hx0' : x = 0
    · subst hx0'
      simp only [mul_zero, add_zero]
      exact mul_pos h0pos hL0
    · have hxpos : 0 < x := lt_of_le_of_ne hx0 (Ne.symm hx0')
      have h1 : 0 ≤ h0 * (L - x) := mul_nonneg (le_of_lt h0pos) (sub_nonneg.mpr hxL)
      have h2 : 0 < hL * x := mul_pos hLpos hxpos
      have heq : h0 * L + (hL - h0) * x = h0 * (L - x) + hL * x := by ring
      linarith
  have heq : h0 + (hL - h0) * x / L = (h0 * L + (hL - h0) * x) / L := by
    field_simp
  rw [heq]
  exact div_pos hnum hL0

private lemma hasDerivAt_sliderFilm {h0 hL L x : ℝ} :
    HasDerivAt (sliderFilm h0 hL L) ((hL - h0) / L) x := by
  have hfun : sliderFilm h0 hL L = fun x => h0 + ((hL - h0) / L) * x := by
    funext y
    unfold sliderFilm
    ring
  rw [hfun]
  have h1 : HasDerivAt (fun y : ℝ => ((hL - h0) / L) * y) (((hL - h0) / L) * 1) x :=
    HasDerivAt.const_mul _ (hasDerivAt_id x)
  simp only [mul_one] at h1
  exact HasDerivAt.const_add _ h1

private lemma sliderFilm_zero {h0 hL L : ℝ} : sliderFilm h0 hL L 0 = h0 := by
  unfold sliderFilm
  simp

private lemma sliderFilm_right {h0 hL L : ℝ} (hL0 : 0 < L) : sliderFilm h0 hL L L = hL := by
  have hLne : L ≠ 0 := ne_of_gt hL0
  unfold sliderFilm
  field_simp
  ring

private lemma const_of_hasDerivAt_zero {f : ℝ → ℝ} {L : ℝ}
    (hf : ∀ x ∈ Set.Icc 0 L, HasDerivAt f 0 x) :
    ∀ x ∈ Set.Icc 0 L, f x = f 0 := by
  intro x hx
  obtain ⟨hx0, hxL⟩ := hx
  have h1 : ∀ y ∈ Set.uIcc 0 x, HasDerivAt f ((fun _ : ℝ => (0 : ℝ)) y) y := by
    intro y hy
    rw [Set.uIcc_of_le hx0] at hy
    obtain ⟨hy0, hyx⟩ := hy
    exact hf y ⟨hy0, le_trans hyx hxL⟩
  have h2 : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) MeasureTheory.volume 0 x :=
    intervalIntegrable_const
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt h1 h2
  simp only [intervalIntegral.integral_const, smul_zero] at hInt
  exact sub_eq_zero.mp hInt.symm

/-! ### A.2. Solution of the Reynolds model -/

/-- Existence: for positive end thicknesses `h0 ≠ hL` and `L > 0`, the closed-form pressure,
with the closed-form gradient, solves the stated Reynolds model. -/
lemma sliderPressure_isReynoldsSolution {μ U h0 hL L : ℝ} (h0pos : 0 < h0) (hLpos : 0 < hL)
    (hne : h0 ≠ hL) (hL0 : 0 < L) :
    IsReynoldsSolution μ U h0 hL L (sliderPressure μ U h0 hL L)
      (sliderPressureGradient μ U h0 hL L) := by
  unfold IsReynoldsSolution
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hsum_ne : h0 + hL ≠ 0 := ne_of_gt (add_pos h0pos hLpos)
  have hdiff_ne : h0 - hL ≠ 0 := sub_ne_zero.mpr hne
  have hsq_ne : h0 ^ 2 - hL ^ 2 ≠ 0 := by
    have hfac : h0 ^ 2 - hL ^ 2 = (h0 - hL) * (h0 + hL) := by ring
    rw [hfac]
    exact mul_ne_zero hdiff_ne hsum_ne
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hx
    have hfilm_ne : sliderFilm h0 hL L x ≠ 0 := ne_of_gt hpos
    have hh : HasDerivAt (sliderFilm h0 hL L) ((hL - h0) / L) x := hasDerivAt_sliderFilm
    have h1 : HasDerivAt (fun y => h0 - sliderFilm h0 hL L y) (0 - (hL - h0) / L) x :=
      (hasDerivAt_const x h0).sub hh
    have h2 : HasDerivAt (fun y => sliderFilm h0 hL L y - hL) ((hL - h0) / L - 0) x :=
      hh.sub (hasDerivAt_const x hL)
    have h3 : HasDerivAt (fun y => (h0 - sliderFilm h0 hL L y) * (sliderFilm h0 hL L y - hL))
        ((0 - (hL - h0) / L) * (sliderFilm h0 hL L x - hL) +
          (h0 - sliderFilm h0 hL L x) * ((hL - h0) / L - 0)) x :=
      h1.mul h2
    have hN : HasDerivAt
        (fun y => (6 * μ * U * L) * ((h0 - sliderFilm h0 hL L y) * (sliderFilm h0 hL L y - hL)))
        ((6 * μ * U * L) * ((0 - (hL - h0) / L) * (sliderFilm h0 hL L x - hL) +
          (h0 - sliderFilm h0 hL L x) * ((hL - h0) / L - 0))) x :=
      h3.const_mul _
    have hD2' : HasDerivAt (fun y => sliderFilm h0 hL L y * sliderFilm h0 hL L y)
        (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)) x :=
      hh.mul hh
    have hD2 : HasDerivAt (fun y => sliderFilm h0 hL L y ^ 2)
        (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)) x :=
      hD2'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
        change sliderFilm h0 hL L y ^ 2 = sliderFilm h0 hL L y * sliderFilm h0 hL L y
        ring))
    have hD : HasDerivAt (fun y => (h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L y ^ 2)
        ((h0 ^ 2 - hL ^ 2) *
          (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L))) x :=
      hD2.const_mul _
    have hDne : (h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L x ^ 2 ≠ 0 :=
      mul_ne_zero hsq_ne (pow_ne_zero 2 hfilm_ne)
    have hp0 := hN.div hD hDne
    have hF'eq : (((6 * μ * U * L) * ((0 - (hL - h0) / L) * (sliderFilm h0 hL L x - hL) +
          (h0 - sliderFilm h0 hL L x) * ((hL - h0) / L - 0))) *
          ((h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L x ^ 2) -
          ((6 * μ * U * L) * ((h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL))) *
          ((h0 ^ 2 - hL ^ 2) *
            (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)))) /
          ((h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L x ^ 2) ^ 2 =
        sliderPressureGradient μ U h0 hL L x := by
      unfold sliderPressureGradient
      field_simp
      ring
    rw [← hF'eq]
    exact hp0.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
      change sliderPressure μ U h0 hL L y =
        ((fun y => (6 * μ * U * L) * ((h0 - sliderFilm h0 hL L y) * (sliderFilm h0 hL L y - hL))) /
          (fun y => (h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L y ^ 2)) y
      unfold sliderPressure
      simp only [Pi.div_apply]
      ring))
  · intro x hx
    have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hx
    have hfilm_ne : sliderFilm h0 hL L x ≠ 0 := ne_of_gt hpos
    have hh : HasDerivAt (sliderFilm h0 hL L) ((hL - h0) / L) x := hasDerivAt_sliderFilm
    have hev := hh.continuousAt.eventually_ne hfilm_ne
    have hsub : HasDerivAt (fun y => sliderFilm h0 hL L y - 2 * h0 * hL / (h0 + hL))
        ((hL - h0) / L - 0) x :=
      hh.sub (hasDerivAt_const x (2 * h0 * hL / (h0 + hL)))
    have hRHS0 : HasDerivAt
        (fun y => (6 * μ * U) * (sliderFilm h0 hL L y - 2 * h0 * hL / (h0 + hL)))
        ((6 * μ * U) * ((hL - h0) / L - 0)) x :=
      hsub.const_mul _
    have hval : (6 * μ * U) * ((hL - h0) / L - 0) = 6 * μ * U * ((hL - h0) / L) := by ring
    rw [hval] at hRHS0
    exact hRHS0.congr_of_eventuallyEq (hev.mono (fun y hy => by
      change sliderFilm h0 hL L y ^ 3 * sliderPressureGradient μ U h0 hL L y =
        (6 * μ * U) * (sliderFilm h0 hL L y - 2 * h0 * hL / (h0 + hL))
      unfold sliderPressureGradient
      field_simp))
  · have h0eq : sliderFilm h0 hL L 0 = h0 := sliderFilm_zero
    unfold sliderPressure
    rw [h0eq]
    simp
  · have hLeq : sliderFilm h0 hL L L = hL := sliderFilm_right hL0
    unfold sliderPressure
    rw [hLeq]
    simp

/-- Uniqueness: for positive end thicknesses `h0 ≠ hL` and `L > 0`, every solution of the
stated Reynolds model is the closed-form pressure on `[0, L]`. -/
lemma isReynoldsSolution_unique {μ U h0 hL L : ℝ} {p p' : ℝ → ℝ} (h0pos : 0 < h0)
    (hLpos : 0 < hL) (hne : h0 ≠ hL) (hL0 : 0 < L)
    (hp : IsReynoldsSolution μ U h0 hL L p p') :
    ∀ x ∈ Set.Icc 0 L, p x = sliderPressure μ U h0 hL L x := by
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  have hP := sliderPressure_isReynoldsSolution (μ := μ) (U := U) h0pos hLpos hne hL0
  obtain ⟨hP1, hP2, hP3, hP4⟩ := hP
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hdiff_ne : h0 - hL ≠ 0 := sub_ne_zero.mpr hne
  have hsq_ne : h0 ^ 2 - hL ^ 2 ≠ 0 := by
    have hfac : h0 ^ 2 - hL ^ 2 = (h0 - hL) * (h0 + hL) := by ring
    rw [hfac]
    exact mul_ne_zero hdiff_ne (ne_of_gt (add_pos h0pos hLpos))
  have hslope_ne : (hL - h0) / L ≠ 0 :=
    div_ne_zero (sub_ne_zero.mpr (Ne.symm hne)) hLne
  have hq : ∀ x ∈ Set.Icc 0 L,
      HasDerivAt (fun y => sliderFilm h0 hL L y ^ 3 * p' y - sliderFilm h0 hL L y ^ 3 *
        sliderPressureGradient μ U h0 hL L y) 0 x := by
    intro x hx
    have hKK : (6 * μ * U * ((hL - h0) / L)) - (6 * μ * U * ((hL - h0) / L)) = 0 :=
      sub_self _
    have h' : HasDerivAt (fun y => sliderFilm h0 hL L y ^ 3 * p' y - sliderFilm h0 hL L y ^ 3 *
        sliderPressureGradient μ U h0 hL L y)
        ((6 * μ * U * ((hL - h0) / L)) - (6 * μ * U * ((hL - h0) / L))) x :=
      (hp2 x hx).sub (hP2 x hx)
    rw [hKK] at h'
    exact h'
  have hqconst : ∀ x ∈ Set.Icc 0 L,
      (sliderFilm h0 hL L x ^ 3 * p' x - sliderFilm h0 hL L x ^ 3 *
        sliderPressureGradient μ U h0 hL L x) =
      (sliderFilm h0 hL L 0 ^ 3 * p' 0 - sliderFilm h0 hL L 0 ^ 3 *
        sliderPressureGradient μ U h0 hL L 0) :=
    const_of_hasDerivAt_zero hq
  set C := sliderFilm h0 hL L 0 ^ 3 * p' 0 - sliderFilm h0 hL L 0 ^ 3 *
    sliderPressureGradient μ U h0 hL L 0
  have hG : ∀ x ∈ Set.Icc 0 L,
      HasDerivAt (fun y => (-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L y ^ 2)⁻¹)
        ((sliderFilm h0 hL L x ^ 3)⁻¹) x := by
    intro x hx
    have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hx
    have hfilm_ne : sliderFilm h0 hL L x ≠ 0 := ne_of_gt hpos
    have hh : HasDerivAt (sliderFilm h0 hL L) ((hL - h0) / L) x := hasDerivAt_sliderFilm
    have hD2' : HasDerivAt (fun y => sliderFilm h0 hL L y * sliderFilm h0 hL L y)
        (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)) x :=
      hh.mul hh
    have hD2 : HasDerivAt (fun y => sliderFilm h0 hL L y ^ 2)
        (((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)) x :=
      hD2'.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun y => by
        change sliderFilm h0 hL L y ^ 2 = sliderFilm h0 hL L y * sliderFilm h0 hL L y
        ring))
    have hD2ne : sliderFilm h0 hL L x ^ 2 ≠ 0 := pow_ne_zero 2 hfilm_ne
    have hinv : HasDerivAt (fun y => (sliderFilm h0 hL L y ^ 2)⁻¹)
        (-(((hL - h0) / L) * sliderFilm h0 hL L x + sliderFilm h0 hL L x * ((hL - h0) / L)) /
          (sliderFilm h0 hL L x ^ 2) ^ 2) x :=
      hD2.inv hD2ne
    have hG0 : HasDerivAt (fun y => (-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L y ^ 2)⁻¹)
        ((-(1 / (2 * ((hL - h0) / L)))) * (-(((hL - h0) / L) * sliderFilm h0 hL L x +
          sliderFilm h0 hL L x * ((hL - h0) / L)) / (sliderFilm h0 hL L x ^ 2) ^ 2)) x :=
      hinv.const_mul _
    have hG'eq : ((-(1 / (2 * ((hL - h0) / L)))) * (-(((hL - h0) / L) * sliderFilm h0 hL L x +
          sliderFilm h0 hL L x * ((hL - h0) / L)) / (sliderFilm h0 hL L x ^ 2) ^ 2)) =
        (sliderFilm h0 hL L x ^ 3)⁻¹ := by
      field_simp
      ring
    rw [hG'eq] at hG0
    exact hG0
  have hr : ∀ x ∈ Set.Icc 0 L,
      HasDerivAt (fun y => (p y - sliderPressure μ U h0 hL L y) - C *
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L y ^ 2)⁻¹)) 0 x := by
    intro x hx
    have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hx
    have hfilm_ne : sliderFilm h0 hL L x ≠ 0 := ne_of_gt hpos
    have hsub1 : HasDerivAt (fun y => p y - sliderPressure μ U h0 hL L y)
        (p' x - sliderPressureGradient μ U h0 hL L x) x :=
      (hp1 x hx).sub (hP1 x hx)
    have hCG : HasDerivAt
        (fun y => C * ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L y ^ 2)⁻¹))
        (C * (sliderFilm h0 hL L x ^ 3)⁻¹) x :=
      (hG x hx).const_mul C
    have hr0 : HasDerivAt
        (fun y => (p y - sliderPressure μ U h0 hL L y) - C *
          ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L y ^ 2)⁻¹))
        ((p' x - sliderPressureGradient μ U h0 hL L x) - C * (sliderFilm h0 hL L x ^ 3)⁻¹) x :=
      hsub1.sub hCG
    have hqC : sliderFilm h0 hL L x ^ 3 * p' x - sliderFilm h0 hL L x ^ 3 *
        sliderPressureGradient μ U h0 hL L x = C := hqconst x hx
    have hfilm3_ne : sliderFilm h0 hL L x ^ 3 ≠ 0 := pow_ne_zero 3 hfilm_ne
    have hr'eq : (p' x - sliderPressureGradient μ U h0 hL L x) -
        C * (sliderFilm h0 hL L x ^ 3)⁻¹ = 0 := by
      field_simp
      linear_combination hqC
    rw [hr'eq] at hr0
    exact hr0
  have hrconst : ∀ x ∈ Set.Icc 0 L,
      ((p x - sliderPressure μ U h0 hL L x) - C *
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L x ^ 2)⁻¹)) =
      ((p 0 - sliderPressure μ U h0 hL L 0) - C *
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹)) :=
    const_of_hasDerivAt_zero hr
  have hGdiff_ne : ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L L ^ 2)⁻¹) -
      ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹) ≠ 0 := by
    have hfilmL : sliderFilm h0 hL L L = hL := sliderFilm_right hL0
    have hfilm0 : sliderFilm h0 hL L 0 = h0 := sliderFilm_zero
    have ha : hL ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hLpos)
    have hb : h0 ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt h0pos)
    have h2s_ne : 2 * ((hL - h0) / L) ≠ 0 := mul_ne_zero (by norm_num) hslope_ne
    have hc_ne : (-(1 / (2 * ((hL - h0) / L)))) ≠ 0 :=
      neg_ne_zero.mpr (div_ne_zero one_ne_zero h2s_ne)
    have hsub_inv_ne : (hL ^ 2)⁻¹ - (h0 ^ 2)⁻¹ ≠ 0 := by
      have heq : (hL ^ 2)⁻¹ - (h0 ^ 2)⁻¹ = (h0 ^ 2 - hL ^ 2) / (hL ^ 2 * h0 ^ 2) := by
        field_simp
      rw [heq]
      exact div_ne_zero hsq_ne (mul_ne_zero ha hb)
    have hGdiff : ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L L ^ 2)⁻¹) -
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹) =
        (-(1 / (2 * ((hL - h0) / L)))) * ((hL ^ 2)⁻¹ - (h0 ^ 2)⁻¹) := by
      rw [hfilmL, hfilm0]
      ring
    rw [hGdiff]
    exact mul_ne_zero hc_ne hsub_inv_ne
  have hLmem : L ∈ Set.Icc 0 L := ⟨le_of_lt hL0, le_rfl⟩
  have hrL := hrconst L hLmem
  have hrL' : (p L - sliderPressure μ U h0 hL L L) - C *
      ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L L ^ 2)⁻¹) =
      (p 0 - sliderPressure μ U h0 hL L 0) - C *
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹) := hrL
  rw [hp3, hP3, hp4, hP4] at hrL'
  have hCeq : C * (((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L L ^ 2)⁻¹) -
      ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹)) = 0 := by
    linear_combination -hrL'
  have hC0 : C = 0 := by
    rcases mul_eq_zero.mp hCeq with h | h
    · exact h
    · exact absurd h hGdiff_ne
  intro x hx
  have hrx := hrconst x hx
  have hrx' : (p x - sliderPressure μ U h0 hL L x) - C *
      ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L x ^ 2)⁻¹) =
      (p 0 - sliderPressure μ U h0 hL L 0) - C *
        ((-(1 / (2 * ((hL - h0) / L)))) * (sliderFilm h0 hL L 0 ^ 2)⁻¹) := hrx
  rw [hC0, hp3, hP3] at hrx'
  simp only [zero_mul, sub_zero, sub_self] at hrx'
  exact sub_eq_zero.mp hrx'

/-! ### A.3. Positivity and load for the converging film -/

/-- For the converging film `h0 > hL > 0` with `μ, U, L > 0` the pressure is positive inside
the slider. -/
lemma sliderPressure_pos {μ U h0 hL L x : ℝ} (hμ : 0 < μ) (hU : 0 < U) (hL0 : 0 < L)
    (hLpos : 0 < hL) (hconv : hL < h0) (hx : x ∈ Set.Ioo 0 L) :
    0 < sliderPressure μ U h0 hL L x := by
  have h0pos : 0 < h0 := lt_trans hLpos hconv
  have hLne : L ≠ 0 := ne_of_gt hL0
  obtain ⟨hx0, hxL⟩ := hx
  have hxIcc : x ∈ Set.Icc 0 L := ⟨le_of_lt hx0, le_of_lt hxL⟩
  have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hxIcc
  have hdiff : 0 < h0 - hL := sub_pos.mpr hconv
  have e1 : h0 - sliderFilm h0 hL L x = (h0 - hL) * x / L := by
    unfold sliderFilm
    field_simp
    ring
  have e2 : sliderFilm h0 hL L x - hL = (h0 - hL) * (L - x) / L := by
    unfold sliderFilm
    field_simp
    ring
  have g1 : 0 < h0 - sliderFilm h0 hL L x := by
    rw [e1]
    exact div_pos (mul_pos hdiff hx0) hL0
  have g2 : 0 < sliderFilm h0 hL L x - hL := by
    rw [e2]
    exact div_pos (mul_pos hdiff (sub_pos.mpr hxL)) hL0
  have g3 : 0 < h0 ^ 2 - hL ^ 2 := by
    have hfac : h0 ^ 2 - hL ^ 2 = (h0 - hL) * (h0 + hL) := by ring
    rw [hfac]
    exact mul_pos hdiff (add_pos h0pos hLpos)
  have g4 : 0 < sliderFilm h0 hL L x ^ 2 := pow_pos hpos 2
  have n1 : (0 : ℝ) < 6 * μ * U * L :=
    mul_pos (mul_pos (mul_pos (by norm_num) hμ) hU) hL0
  unfold sliderPressure
  refine div_pos ?_ (mul_pos g3 g4)
  exact mul_pos (mul_pos n1 g1) g2

/-- Load per unit width in closed form, for positive end thicknesses `h0 ≠ hL` and `L > 0`:
`W = 6 μ U L² / (h0 - hL)² (log (h0 / hL) - 2 (h0 - hL) / (h0 + hL))`. -/
lemma sliderLoad_eq {μ U h0 hL L : ℝ} (h0pos : 0 < h0) (hLpos : 0 < hL) (hne : h0 ≠ hL)
    (hL0 : 0 < L) :
    sliderLoad μ U h0 hL L =
      6 * μ * U * L ^ 2 / (h0 - hL) ^ 2 *
        (Real.log (h0 / hL) - 2 * (h0 - hL) / (h0 + hL)) := by
  have hLne : L ≠ 0 := ne_of_gt hL0
  have h0ne : h0 ≠ 0 := ne_of_gt h0pos
  have hLne' : hL ≠ 0 := ne_of_gt hLpos
  have hsum_ne : h0 + hL ≠ 0 := ne_of_gt (add_pos h0pos hLpos)
  have hdiff_ne : h0 - hL ≠ 0 := sub_ne_zero.mpr hne
  have hLH_ne : hL - h0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hsq_ne : h0 ^ 2 - hL ^ 2 ≠ 0 := by
    have hfac : h0 ^ 2 - hL ^ 2 = (h0 - hL) * (h0 + hL) := by ring
    rw [hfac]
    exact mul_ne_zero hdiff_ne hsum_ne
  have hP := sliderPressure_isReynoldsSolution (μ := μ) (U := U) h0pos hLpos hne hL0
  obtain ⟨hP1, -, -, -⟩ := hP
  have hΦ : ∀ y ∈ Set.uIcc 0 L,
      HasDerivAt (fun t => (6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
        (-sliderFilm h0 hL L t + (h0 + hL) * Real.log (sliderFilm h0 hL L t) +
          (h0 * hL) / (sliderFilm h0 hL L t)))
        ((sliderPressure μ U h0 hL L) y) y := by
    intro y hy
    rw [Set.uIcc_of_le (le_of_lt hL0)] at hy
    have hpos : 0 < sliderFilm h0 hL L y := sliderFilm_pos h0pos hLpos hL0 hy
    have hfilm_ne : sliderFilm h0 hL L y ≠ 0 := ne_of_gt hpos
    have hh : HasDerivAt (sliderFilm h0 hL L) ((hL - h0) / L) y := hasDerivAt_sliderFilm
    have h1 : HasDerivAt (fun t => -sliderFilm h0 hL L t) (-((hL - h0) / L)) y := hh.neg
    have hlog : HasDerivAt (fun t => Real.log (sliderFilm h0 hL L t))
        (((hL - h0) / L) / sliderFilm h0 hL L y) y :=
      hh.log hfilm_ne
    have h2 : HasDerivAt (fun t => (h0 + hL) * Real.log (sliderFilm h0 hL L t))
        ((h0 + hL) * (((hL - h0) / L) / sliderFilm h0 hL L y)) y :=
      hlog.const_mul _
    have h3 : HasDerivAt (fun t => (h0 * hL) / (sliderFilm h0 hL L t))
        ((0 * sliderFilm h0 hL L y - (h0 * hL) * ((hL - h0) / L)) /
          (sliderFilm h0 hL L y) ^ 2) y :=
      (hasDerivAt_const y (h0 * hL)).div hh hfilm_ne
    have h12 : HasDerivAt
        (fun t => -sliderFilm h0 hL L t + (h0 + hL) * Real.log (sliderFilm h0 hL L t))
        ((-((hL - h0) / L)) + (h0 + hL) * (((hL - h0) / L) / sliderFilm h0 hL L y)) y :=
      h1.add h2
    have h123 : HasDerivAt
        (fun t => -sliderFilm h0 hL L t + (h0 + hL) * Real.log (sliderFilm h0 hL L t) +
          (h0 * hL) / (sliderFilm h0 hL L t))
        (((-((hL - h0) / L)) + (h0 + hL) * (((hL - h0) / L) / sliderFilm h0 hL L y)) +
          ((0 * sliderFilm h0 hL L y - (h0 * hL) * ((hL - h0) / L)) /
            (sliderFilm h0 hL L y) ^ 2)) y :=
      h12.add h3
    have hΦ0 : HasDerivAt
        (fun t => (6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
          (-sliderFilm h0 hL L t + (h0 + hL) * Real.log (sliderFilm h0 hL L t) +
            (h0 * hL) / (sliderFilm h0 hL L t)))
        ((6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
          (((-((hL - h0) / L)) + (h0 + hL) * (((hL - h0) / L) / sliderFilm h0 hL L y)) +
            ((0 * sliderFilm h0 hL L y - (h0 * hL) * ((hL - h0) / L)) /
              (sliderFilm h0 hL L y) ^ 2))) y :=
      h123.const_mul _
    have hΦ'eq : (6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
          (((-((hL - h0) / L)) + (h0 + hL) * (((hL - h0) / L) / sliderFilm h0 hL L y)) +
            ((0 * sliderFilm h0 hL L y - (h0 * hL) * ((hL - h0) / L)) /
              (sliderFilm h0 hL L y) ^ 2)) =
        sliderPressure μ U h0 hL L y := by
      unfold sliderPressure
      field_simp
      ring
    rw [hΦ'eq] at hΦ0
    exact hΦ0
  have hPcontIcc : ContinuousOn (sliderPressure μ U h0 hL L) (Set.Icc 0 L) := by
    intro y hy
    exact ((hP1 y hy).continuousAt).continuousWithinAt
  have hPcont : ContinuousOn (sliderPressure μ U h0 hL L) (Set.uIcc 0 L) := by
    rw [Set.uIcc_of_le (le_of_lt hL0)]
    exact hPcontIcc
  have hPint : IntervalIntegrable (sliderPressure μ U h0 hL L) MeasureTheory.volume 0 L :=
    hPcont.intervalIntegrable
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt hΦ hPint
  have hLoad : sliderLoad μ U h0 hL L =
      (6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
        (-sliderFilm h0 hL L L + (h0 + hL) * Real.log (sliderFilm h0 hL L L) +
          (h0 * hL) / (sliderFilm h0 hL L L)) -
      (6 * μ * U * L ^ 2 / ((h0 ^ 2 - hL ^ 2) * (hL - h0))) *
        (-sliderFilm h0 hL L 0 + (h0 + hL) * Real.log (sliderFilm h0 hL L 0) +
          (h0 * hL) / (sliderFilm h0 hL L 0)) := hInt
  rw [hLoad, sliderFilm_right hL0, sliderFilm_zero, Real.log_div h0ne hLne']
  field_simp
  ring

/-- For the converging film `h0 > hL > 0` with `μ, U, L > 0` the load per unit width is
positive. -/
lemma sliderLoad_pos {μ U h0 hL L : ℝ} (hμ : 0 < μ) (hU : 0 < U) (hL0 : 0 < L)
    (hLpos : 0 < hL) (hconv : hL < h0) :
    0 < sliderLoad μ U h0 hL L := by
  have h0pos : 0 < h0 := lt_trans hLpos hconv
  have hne : h0 ≠ hL := ne_of_gt hconv
  have hP := sliderPressure_isReynoldsSolution (μ := μ) (U := U) h0pos hLpos hne hL0
  obtain ⟨hP1, -, -, hP4⟩ := hP
  have hcont : ContinuousOn (sliderPressure μ U h0 hL L) (Set.Icc 0 L) := by
    intro y hy
    exact ((hP1 y hy).continuousAt).continuousWithinAt
  have hnonneg : ∀ x ∈ Set.Ioc 0 L, 0 ≤ sliderPressure μ U h0 hL L x := by
    intro x hx
    obtain ⟨hx0, hxL⟩ := hx
    by_cases h : x < L
    · exact le_of_lt (sliderPressure_pos hμ hU hL0 hLpos hconv ⟨hx0, h⟩)
    · have hxeq : x = L := le_antisymm hxL (not_lt.mp h)
      subst hxeq
      rw [hP4]
  have hmid : L / 2 ∈ Set.Ioo 0 L := ⟨by linarith, by linarith⟩
  have hex : ∃ c ∈ Set.Icc 0 L, 0 < sliderPressure μ U h0 hL L c :=
    ⟨L / 2, ⟨le_of_lt hmid.1, le_of_lt hmid.2⟩,
      sliderPressure_pos hμ hU hL0 hLpos hconv hmid⟩
  unfold sliderLoad
  exact intervalIntegral.integral_pos hL0 hcont hnonneg hex

/-! ### A.4. Diverging and closed films -/

/-- A diverging film `0 < h0 < hL` with `μ, U, L > 0` gives negative pressure inside the
slider, so the no-cavitation model fails there. -/
lemma sliderPressure_neg_of_diverging {μ U h0 hL L x : ℝ} (hμ : 0 < μ) (hU : 0 < U)
    (hL0 : 0 < L) (h0pos : 0 < h0) (hdiv : h0 < hL) (hx : x ∈ Set.Ioo 0 L) :
    sliderPressure μ U h0 hL L x < 0 := by
  have hLpos : 0 < hL := lt_trans h0pos hdiv
  have hLne : L ≠ 0 := ne_of_gt hL0
  obtain ⟨hx0, hxL⟩ := hx
  have hxIcc : x ∈ Set.Icc 0 L := ⟨le_of_lt hx0, le_of_lt hxL⟩
  have hpos : 0 < sliderFilm h0 hL L x := sliderFilm_pos h0pos hLpos hL0 hxIcc
  have hdiff : h0 - hL < 0 := sub_neg.mpr hdiv
  have e1 : h0 - sliderFilm h0 hL L x = (h0 - hL) * x / L := by
    unfold sliderFilm
    field_simp
    ring
  have e2 : sliderFilm h0 hL L x - hL = (h0 - hL) * (L - x) / L := by
    unfold sliderFilm
    field_simp
    ring
  have g1 : h0 - sliderFilm h0 hL L x < 0 := by
    rw [e1]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hdiff hx0) hL0
  have g2 : sliderFilm h0 hL L x - hL < 0 := by
    rw [e2]
    exact div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hdiff (sub_pos.mpr hxL)) hL0
  have g3 : h0 ^ 2 - hL ^ 2 < 0 := by
    have hfac : h0 ^ 2 - hL ^ 2 = (h0 - hL) * (h0 + hL) := by ring
    rw [hfac]
    exact mul_neg_of_neg_of_pos hdiff (add_pos h0pos hLpos)
  have g4 : 0 < sliderFilm h0 hL L x ^ 2 := pow_pos hpos 2
  have n1 : (0 : ℝ) < 6 * μ * U * L :=
    mul_pos (mul_pos (mul_pos (by norm_num) hμ) hU) hL0
  have npos : 0 < 6 * μ * U * L * (h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL) := by
    have hprod : 0 < (h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL) :=
      mul_pos_of_neg_of_neg g1 g2
    have heq : 6 * μ * U * L * (h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL) =
        (6 * μ * U * L) * ((h0 - sliderFilm h0 hL L x) * (sliderFilm h0 hL L x - hL)) := by
      ring
    rw [heq]
    exact mul_pos n1 hprod
  have dneg : (h0 ^ 2 - hL ^ 2) * sliderFilm h0 hL L x ^ 2 < 0 := mul_neg_of_neg_of_pos g3 g4
  unfold sliderPressure
  exact div_neg_of_pos_of_neg npos dneg

/-- An outlet thickness `hL = 0` is rejected: for `h0, μ, U, L > 0` the stated Reynolds model
with the film closing at `x = L` has no solution. -/
lemma not_isReynoldsSolution_of_hL_eq_zero {μ U h0 L : ℝ} {p p' : ℝ → ℝ} (hμ : 0 < μ)
    (hU : 0 < U) (h0pos : 0 < h0) (hL0 : 0 < L) :
    ¬ IsReynoldsSolution μ U h0 0 L p p' := by
  intro hp
  obtain ⟨hp1, hp2, hp3, hp4⟩ := hp
  have hLne : L ≠ 0 := ne_of_gt hL0
  have hr0 : ∀ x ∈ Set.Icc 0 L,
      HasDerivAt (fun y => sliderFilm h0 0 L y ^ 3 * p' y - (6 * μ * U) * sliderFilm h0 0 L y)
        0 x := by
    intro x hx
    have h6 : HasDerivAt (fun y => (6 * μ * U) * sliderFilm h0 0 L y)
        ((6 * μ * U) * ((0 - h0) / L)) x :=
      HasDerivAt.const_mul _ hasDerivAt_sliderFilm
    have hKK : (6 * μ * U * ((0 - h0) / L)) - (6 * μ * U) * ((0 - h0) / L) = 0 := by ring
    have h' : HasDerivAt
        (fun y => sliderFilm h0 0 L y ^ 3 * p' y - (6 * μ * U) * sliderFilm h0 0 L y)
        ((6 * μ * U * ((0 - h0) / L)) - (6 * μ * U) * ((0 - h0) / L)) x :=
      (hp2 x hx).sub h6
    rw [hKK] at h'
    exact h'
  have hrconst : ∀ x ∈ Set.Icc 0 L,
      (sliderFilm h0 0 L x ^ 3 * p' x - (6 * μ * U) * sliderFilm h0 0 L x) =
      (sliderFilm h0 0 L 0 ^ 3 * p' 0 - (6 * μ * U) * sliderFilm h0 0 L 0) :=
    const_of_hasDerivAt_zero hr0
  have hfilmL0 : sliderFilm h0 0 L L = 0 := sliderFilm_right hL0
  have hLmem : L ∈ Set.Icc 0 L := ⟨le_of_lt hL0, le_rfl⟩
  have hrL := hrconst L hLmem
  have hrL' : sliderFilm h0 0 L L ^ 3 * p' L - (6 * μ * U) * sliderFilm h0 0 L L =
      sliderFilm h0 0 L 0 ^ 3 * p' 0 - (6 * μ * U) * sliderFilm h0 0 L 0 := hrL
  rw [hfilmL0] at hrL'
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, mul_zero,
    sub_self] at hrL'
  have hr0eq : sliderFilm h0 0 L 0 ^ 3 * p' 0 - (6 * μ * U) * sliderFilm h0 0 L 0 = 0 :=
    hrL'.symm
  have hr_zero : ∀ y ∈ Set.Icc 0 L,
      sliderFilm h0 0 L y ^ 3 * p' y - (6 * μ * U) * sliderFilm h0 0 L y = 0 := by
    intro y hy
    have h2 : sliderFilm h0 0 L y ^ 3 * p' y - (6 * μ * U) * sliderFilm h0 0 L y =
        sliderFilm h0 0 L 0 ^ 3 * p' 0 - (6 * μ * U) * sliderFilm h0 0 L 0 :=
      hrconst y hy
    rw [hr0eq] at h2
    exact h2
  have hcont : ContinuousOn p (Set.Icc 0 L) := by
    intro y hy
    exact ((hp1 y hy).continuousAt).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo 0 L, HasDerivAt p (p' x) x := by
    intro x hx
    obtain ⟨hx0, hxL⟩ := hx
    exact hp1 x ⟨le_of_lt hx0, le_of_lt hxL⟩
  obtain ⟨c, hcIoo, hceq⟩ := exists_hasDerivAt_eq_slope p p' hL0 hcont hderiv
  obtain ⟨hc0, hcL⟩ := hcIoo
  have hcIcc : c ∈ Set.Icc 0 L := ⟨le_of_lt hc0, le_of_lt hcL⟩
  have hposc : 0 < sliderFilm h0 0 L c := by
    have e : sliderFilm h0 0 L c = h0 * (L - c) / L := by
      unfold sliderFilm
      field_simp
      ring
    rw [e]
    exact div_pos (mul_pos h0pos (sub_pos.mpr hcL)) hL0
  have hnec : sliderFilm h0 0 L c ≠ 0 := ne_of_gt hposc
  have hry : sliderFilm h0 0 L c ^ 3 * p' c - (6 * μ * U) * sliderFilm h0 0 L c = 0 :=
    hr_zero c hcIcc
  have hmul : p' c * (sliderFilm h0 0 L c) ^ 3 = 6 * μ * U * (sliderFilm h0 0 L c) := by
    linear_combination hry
  have hcancel : p' c * (sliderFilm h0 0 L c) ^ 2 = 6 * μ * U := by
    have h2 : (p' c * (sliderFilm h0 0 L c) ^ 2) * (sliderFilm h0 0 L c) =
        (6 * μ * U) * (sliderFilm h0 0 L c) := by
      linear_combination hmul
    exact mul_right_cancel₀ hnec h2
  have h2ne : (sliderFilm h0 0 L c) ^ 2 ≠ 0 := pow_ne_zero 2 hnec
  have hp'_eq : p' c = 6 * μ * U / ((sliderFilm h0 0 L c) ^ 2) :=
    (eq_div_iff h2ne).mpr hcancel
  have h6pos : (0 : ℝ) < 6 * μ * U := mul_pos (mul_pos (by norm_num) hμ) hU
  have hpos' : 0 < p' c := by
    rw [hp'_eq]
    exact div_pos h6pos (pow_pos hposc 2)
  rw [hp3, hp4] at hceq
  simp at hceq
  linarith

end Elasticity.ContactAndLubrication
