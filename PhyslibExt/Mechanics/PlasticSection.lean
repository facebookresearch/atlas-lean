/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Rectangular plastic section

For a rectangular section in pure bending, the elastic first-yield moment is
`σy * b * h ^ 2 / 6`, the fully plastic moment is `σy * b * h ^ 2 / 4`, and their ratio,
the shape factor, is `3 / 2`.

## i. Overview

Convention lock for a rectangular section in pure bending:

- Section: a rectangle of width `b` and height `h`, symmetric about its neutral axis.
  The through-thickness coordinate `y ∈ [-h / 2, h / 2]` is measured from the neutral
  axis at mid-depth. Physical domain `0 < b`, `0 < h`.
- Stress: the normal (bending) stress `σ y` on the section, tension positive and uniform
  across the width. Yield stress `σy`, physical domain `0 < σy`. Units: `b`, `h`, `y` are
  lengths; `σ`, `σy` are forces per area; the axial resultant is a force and the moment a
  force times a length.
- Elastic first-yield stress (locked definition): the linear distribution
  `firstYieldStress σy h y = σy * (2 * y / h)`, which carries `± σy` at the outer fibers
  `y = ± h / 2` when `h ≠ 0`. Lean totalizes `2 * y / 0 = 0`, so at `h = 0` the
  distribution is identically zero.
- Fully plastic stress block (locked definition): `fullyPlasticStress σy y = σy` for
  `0 ≤ y` and `-σy` for `y < 0`. The value `σy` at the single point `y = 0` is a
  convention: a null set for both integrals below, and multiplied by `y = 0` in the
  moment integrand.
- Resultants, as oriented interval integrals over `[-h / 2, h / 2]` (Mathlib's interval
  integral, which is `0` on non-integrable integrands; both locked distributions are
  bounded and piecewise continuous): axial force
  `sectionForce b h σ = ∫ y in (-h / 2)..(h / 2), b * σ y` and bending moment about the
  neutral axis `sectionMoment b h σ = ∫ y in (-h / 2)..(h / 2), y * (b * σ y)`. For
  `h < 0` the interval is reversed.
- Shape factor: the fully plastic moment divided by the elastic first-yield moment. Real
  division is totalized (`x / 0 = 0`); the shape-factor result assumes `0 < b`, `0 < h`
  and `0 < σy`, which make the denominator nonzero.
- Orientation remark (not a result): in linear elastic Euler-Bernoulli bending with `y`
  positive in the transverse direction in which the beam deflection `w` and the load are
  positive, the plane-section stress is `σ y = M * y / I` with `I = b * h ^ 3 / 12` and
  the sagging-positive moment `M = -EI w''`. Its `sectionMoment` is `M`, and at
  `M = σy * b * h ^ 2 / 6` it is `firstYieldStress σy h`.

The two stress distributions are admitted states, not derived from a constitutive law:
no yield law, no strain, modulus or elastic-plastic transition, and no partially plastic
state. Pure bending only (the zero axial resultants are checked); no biaxial stress and
no axial force-moment interaction surface. No beam, hinge or collapse-load statement.

This is the rectangular case of Jones, *Structural Impact*, §1.2: `z` there is `y` here,
`B` is `b`, `H` is `h`, `σ0` is `σy`, and `M0` is the fully plastic moment `M_p`.

## ii. Key results

- `Mechanics.PlasticSection.firstYieldStress`, `fullyPlasticStress`, `sectionForce`,
  `sectionMoment`: the two admitted stress distributions and their resultants.
- `Mechanics.PlasticSection.sectionForce_firstYieldStress`,
  `sectionForce_fullyPlasticStress`: pure bending, no axial force in either state.
- `Mechanics.PlasticSection.sectionMoment_firstYieldStress`: the elastic first-yield
  moment `σy * b * h ^ 2 / 6`.
- `Mechanics.PlasticSection.sectionMoment_fullyPlasticStress`: the fully plastic moment
  `σy * b * h ^ 2 / 4`.
- `Mechanics.PlasticSection.sectionMoment_fullyPlastic_div_firstYield`: the shape factor
  `3 / 2`.

## iii. Table of contents

- A. Rectangular section resultants

## iv. References

- N. Jones, *Structural Impact*, 2nd edition, Cambridge University Press, 2012, §1.2,
  pp. 2-5, equations (1.3)-(1.6) and Table 1.1: the elastic and fully plastic bending
  moments and the shape factor of a rectangular section.

## A. Rectangular section resultants
-/

@[expose] public section

namespace Mechanics.PlasticSection

/-- Elastic first-yield stress at height `y` (locked definition): the linear distribution
`σy * (2 * y / h)` through a section of height `h`, equal to `σy` at the outer fiber `y = h / 2` and
to `-σy` at `y = -h / 2` when `h ≠ 0` (tension positive). With the convention `x / 0 = 0` it is
identically `0` when `h = 0`. -/
noncomputable def firstYieldStress (σy h y : ℝ) : ℝ :=
  σy * (2 * y / h)

/-- Fully plastic stress block at height `y` (locked definition): `σy` on
the side `0 ≤ y` and `-σy` on the side `y < 0`. The value `σy` at `y = 0`
is a convention on a null set. -/
noncomputable def fullyPlasticStress (σy y : ℝ) : ℝ :=
  if 0 ≤ y then σy else -σy

/-- Axial force resultant `∫ y in (-h / 2)..(h / 2), b * σ y` of a normal stress distribution `σ`
(tension positive) over a rectangular section of width `b` and height `h`, as an oriented interval
integral. It is `0` when the integrand is not integrable on the interval. -/
noncomputable def sectionForce (b h : ℝ) (σ : ℝ → ℝ) : ℝ :=
  ∫ y in (-h / 2)..(h / 2), b * σ y

/-- Bending moment about the neutral axis, `∫ y in (-h / 2)..(h / 2), y * (b * σ y)`, of a normal
stress distribution `σ` (tension positive) over a rectangular section of width `b` and height `h`,
as an oriented interval integral. It is `0` when the integrand is not integrable on the interval. -/
noncomputable def sectionMoment (b h : ℝ) (σ : ℝ → ℝ) : ℝ :=
  ∫ y in (-h / 2)..(h / 2), y * (b * σ y)

private lemma integral_odd_zero (g : ℝ → ℝ) (a : ℝ) (hg : ∀ x, g (-x) = -g x) :
    ∫ x in (-a)..a, g x = 0 := by
  have hcomp : (∫ x in (-a)..a, g (-x)) = ∫ x in (-a)..a, g x := by
    rw [intervalIntegral.integral_comp_neg, neg_neg]
  have hneg : (∫ x in (-a)..a, g (-x)) = -(∫ x in (-a)..a, g x) := by
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr (fun x _ => hg x)
  linarith

/-- The elastic first-yield state carries no axial force: the linear
distribution is odd in `y`, so its resultant over the symmetric section
vanishes, consistent with pure bending about the mid-depth axis. Holds for
all real `b`, `h`, `σy` (oriented integral); the physical reading is
`0 < b`, `0 < h`, `0 < σy`. -/
lemma sectionForce_firstYieldStress (b h σy : ℝ) :
    sectionForce b h (firstYieldStress σy h) = 0 := by
  have hcongr : Set.EqOn (fun y : ℝ => b * (σy * (2 * y / h)))
      (fun y : ℝ => (b * σy * (2 / h)) * y) (Set.uIcc (-h / 2) (h / 2)) := by
    intro y _
    ring
  unfold sectionForce firstYieldStress
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul, integral_id]
  ring

/-- The fully plastic stress block carries no axial force: equal halves of
the symmetric section carry `σy` and `-σy`, consistent with a plastic
neutral axis at mid-depth. Holds for all real `b`, `h`, `σy` (oriented
integral); the physical reading is `0 < b`, `0 < h`, `0 < σy`. -/
lemma sectionForce_fullyPlasticStress (b h σy : ℝ) :
    sectionForce b h (fullyPlasticStress σy) = 0 := by
  have hne : ∀ᵐ x : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp [MeasureTheory.measure_singleton]
  have hae : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∈ Set.uIoc (-h / 2) (h / 2) →
        b * (if 0 ≤ x then σy else -σy) =
          (if 0 < x then b * σy else if x < 0 then b * (-σy) else 0) := by
    filter_upwards [hne] with x hx0 _
    rcases lt_or_gt_of_ne hx0 with hneg | hpos
    · rw [ite_eq_right (not_le.mpr hneg), ite_eq_right (not_lt.mpr hneg.le), ite_eq_left hneg]
    · rw [ite_eq_left hpos.le, ite_eq_left hpos]
  have hodd : ∀ x : ℝ, (if 0 < -x then b * σy else if -x < 0 then b * (-σy) else 0) =
      -(if 0 < x then b * σy else if x < 0 then b * (-σy) else 0) := by
    intro x
    rcases lt_trichotomy x 0 with hneg | heq | hpos
    · have h1 : 0 < -x := by linarith
      rw [ite_eq_left h1, ite_eq_right (not_lt.mpr hneg.le), ite_eq_left hneg]
      ring
    · subst heq
      simp
    · have hle : -x ≤ 0 := by linarith
      have h1 : ¬ 0 < -x := not_lt.mpr hle
      have h2 : -x < 0 := by linarith
      rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left hpos]
      ring
  unfold sectionForce fullyPlasticStress
  rw [intervalIntegral.integral_congr_ae hae]
  have hbd : (-h / 2 : ℝ) = -(h / 2) := by ring
  rw [hbd]
  exact integral_odd_zero _ _ hodd

/-- Elastic first-yield moment of the rectangular section:
`∫ y in (-h / 2)..(h / 2), y * (b * (σy * (2 * y / h))) = σy * b * h ^ 2 / 6`,
the yield stress times the elastic section modulus `b * h ^ 2 / 6`. Holds
for all real `b`, `h`, `σy`; at `h = 0` both sides are `0` (totalized
division). The physical reading is `0 < b`, `0 < h`, `0 < σy`. -/
theorem sectionMoment_firstYieldStress (b h σy : ℝ) :
    sectionMoment b h (firstYieldStress σy h) = σy * b * h ^ 2 / 6 := by
  have hcongr : Set.EqOn (fun y : ℝ => y * (b * (σy * (2 * y / h))))
      (fun y : ℝ => (b * σy * (2 / h)) * y ^ 2) (Set.uIcc (-h / 2) (h / 2)) := by
    intro y _
    ring
  unfold sectionMoment firstYieldStress
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul,
    integral_pow 2]
  norm_num
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  · field_simp
    ring

/-- Fully plastic moment of the rectangular section: for positive height,
the stress block integrates to `σy * b * h ^ 2 / 4`, the yield stress times
the plastic modulus `b * h ^ 2 / 4`. Any real `b` and `σy`; the physical
reading is `0 < b`, `0 < σy`. For `h < 0` the oriented integral is
`-(σy * b * h ^ 2 / 4)`, so the premise `0 < h` cannot be dropped. -/
theorem sectionMoment_fullyPlasticStress {h : ℝ} (b σy : ℝ) (hh : 0 < h) :
    sectionMoment b h (fullyPlasticStress σy) = σy * b * h ^ 2 / 4 := by
  have hFcont : Continuous (fun y : ℝ => y * (b * (if 0 ≤ y then σy else -σy))) := by
    have heq : (fun y : ℝ => y * (b * (if 0 ≤ y then σy else -σy))) =
        (fun y : ℝ => (b * σy) * |y|) := by
      funext y
      by_cases hy0 : 0 ≤ y
      · rw [ite_eq_left hy0, abs_of_nonneg hy0]
        ring
      · have hy0' : y < 0 := not_le.mp hy0
        rw [ite_eq_right (not_le.mpr hy0'), abs_of_neg hy0']
        ring
    rw [heq]
    exact continuous_abs.const_mul _
  have h1 : IntervalIntegrable (fun y : ℝ => y * (b * (if 0 ≤ y then σy else -σy)))
      MeasureTheory.volume (-h / 2) 0 :=
    hFcont.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun y : ℝ => y * (b * (if 0 ≤ y then σy else -σy)))
      MeasureTheory.volume 0 (h / 2) :=
    hFcont.intervalIntegrable _ _
  have e1 : Set.EqOn (fun y : ℝ => y * (b * (if 0 ≤ y then σy else -σy)))
      (fun y : ℝ => y * (b * (-σy))) (Set.uIcc (-h / 2) 0) := by
    have hle : -h / 2 ≤ (0 : ℝ) := by linarith
    intro y hy
    have hy' : y ∈ Set.Icc (-h / 2) 0 := by rwa [Set.uIcc_of_le hle] at hy
    rw [Set.mem_Icc] at hy'
    rcases eq_or_lt_of_le hy'.2 with rfl | hlt
    · show (0 : ℝ) * (b * (if 0 ≤ 0 then σy else -σy)) = 0 * (b * (-σy))
      simp
    · show y * (b * (if 0 ≤ y then σy else -σy)) = y * (b * (-σy))
      rw [ite_eq_right (not_le.mpr hlt)]
  have e2 : Set.EqOn (fun y : ℝ => y * (b * (if 0 ≤ y then σy else -σy)))
      (fun y : ℝ => y * (b * σy)) (Set.uIcc 0 (h / 2)) := by
    have hle : (0 : ℝ) ≤ h / 2 := by linarith
    intro y hy
    have hy' : y ∈ Set.Icc 0 (h / 2) := by rwa [Set.uIcc_of_le hle] at hy
    rw [Set.mem_Icc] at hy'
    show y * (b * (if 0 ≤ y then σy else -σy)) = y * (b * σy)
    rw [ite_eq_left hy'.1]
  unfold sectionMoment fullyPlasticStress
  rw [(intervalIntegral.integral_add_adjacent_intervals h1 h2).symm,
    intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    integral_id, integral_id]
  ring

/-- Shape factor of the rectangular section: for positive width, height and
yield stress, the fully plastic moment divided by the elastic first-yield
moment is `3 / 2`. The premises make the denominator `σy * b * h ^ 2 / 6`
nonzero (real division is totalized) and fix the orientation of the
section. -/
theorem sectionMoment_fullyPlastic_div_firstYield {b h σy : ℝ}
    (hb : 0 < b) (hh : 0 < h) (hσy : 0 < σy) :
    sectionMoment b h (fullyPlasticStress σy) /
        sectionMoment b h (firstYieldStress σy h) = 3 / 2 := by
  rw [sectionMoment_fullyPlasticStress b σy hh, sectionMoment_firstYieldStress b h σy]
  have hne : σy * b * h ^ 2 / 6 ≠ 0 := by positivity
  field_simp
  ring

end Mechanics.PlasticSection
