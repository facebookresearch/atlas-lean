/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Mechanics.PlasticSection
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Rectangular plastic section checks

Concrete consumers of `PhyslibExt.Mechanics.PlasticSection`: the witness section
`b = 1`, `h = 2`, `σy = 3` with first-yield moment `2`, plastic moment `3` and shape
factor `3 / 2`; degenerate controls (`h = 0`, `b = 0`, `σy = 0`, totalized ratio `0`);
outer-fiber values and stress admissibility; independence of the value at `y = 0`;
product forms with the elastic and plastic moduli; and consistency with the flexure
formula `σ = M y / I`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Witness, controls and consistency

## iv. References

- `PhyslibExt.Mechanics.PlasticSection`
-/

open Mechanics.PlasticSection

/-! ## A. Witness, controls and consistency -/

/-- The public statement shapes of the five section results. -/
example (b h σy : ℝ) (hb : 0 < b) (hh : 0 < h) (hσy : 0 < σy) :
    sectionForce b h (firstYieldStress σy h) = 0 ∧
      sectionForce b h (fullyPlasticStress σy) = 0 ∧
      sectionMoment b h (firstYieldStress σy h) = σy * b * h ^ 2 / 6 ∧
      sectionMoment b h (fullyPlasticStress σy) = σy * b * h ^ 2 / 4 ∧
      sectionMoment b h (fullyPlasticStress σy) /
          sectionMoment b h (firstYieldStress σy h) = 3 / 2 :=
  ⟨sectionForce_firstYieldStress b h σy, sectionForce_fullyPlasticStress b h σy,
    sectionMoment_firstYieldStress b h σy, sectionMoment_fullyPlasticStress b σy hh,
    sectionMoment_fullyPlastic_div_firstYield hb hh hσy⟩

/-- Witness `b = 1`, `h = 2`, `σy = 3`: no axial force, first-yield moment `2`, plastic
moment `3`, positive, with ratio `3 / 2`. -/
example :
    sectionForce 1 2 (firstYieldStress 3 2) = 0 ∧
      sectionForce 1 2 (fullyPlasticStress 3) = 0 ∧
      sectionMoment 1 2 (firstYieldStress 3 2) = 2 ∧
      sectionMoment 1 2 (fullyPlasticStress 3) = 3 ∧
      0 < sectionMoment 1 2 (fullyPlasticStress 3) := by
  refine ⟨sectionForce_firstYieldStress 1 2 3, sectionForce_fullyPlasticStress 1 2 3, ?_,
    ?_, ?_⟩
  · rw [sectionMoment_firstYieldStress]
    norm_num
  · rw [sectionMoment_fullyPlasticStress 1 3 (by norm_num)]
    norm_num
  · rw [sectionMoment_fullyPlasticStress 1 3 (by norm_num)]
    norm_num

/-- Degenerate controls: at `h = 0`, `b = 0` or `σy = 0` the moments vanish, and the
totalized shape factor at `b = 0` is `0`. -/
example (b σy : ℝ) :
    sectionMoment b 0 (firstYieldStress σy 0) = 0 ∧
      sectionMoment 0 2 (firstYieldStress σy 2) = 0 ∧
      sectionMoment b 2 (firstYieldStress 0 2) = 0 ∧
      sectionMoment b 2 (fullyPlasticStress 0) = 0 ∧
      sectionMoment 0 2 (fullyPlasticStress σy) /
          sectionMoment 0 2 (firstYieldStress σy 2) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sectionMoment_firstYieldStress]
    ring
  · rw [sectionMoment_firstYieldStress]
    ring
  · rw [sectionMoment_firstYieldStress]
    ring
  · rw [sectionMoment_fullyPlasticStress b 0 (by norm_num)]
    ring
  · rw [sectionMoment_fullyPlasticStress 0 σy (by norm_num), sectionMoment_firstYieldStress]
    norm_num

/-- Outer fibers and the neutral-axis convention at the witness: the linear distribution
carries `±3` at `y = ±1`, and the plastic block takes the conventional value `3` at
`y = 0`. -/
example :
    firstYieldStress 3 2 1 = 3 ∧ firstYieldStress 3 2 (-1) = -3 ∧
      firstYieldStress 3 2 0 = 0 ∧ fullyPlasticStress 3 0 = 3 ∧
      fullyPlasticStress 3 (-1) = -3 := by
  norm_num [firstYieldStress, fullyPlasticStress]

/-- Admissibility: on the section, neither distribution exceeds the yield stress. -/
example {σy h y : ℝ} (hσy : 0 < σy) (hh : 0 < h) (hy : |y| ≤ h / 2) :
    |firstYieldStress σy h y| ≤ σy ∧ |fullyPlasticStress σy y| ≤ σy := by
  constructor
  · have h1 : |2 * y / h| ≤ 1 := by
      rw [abs_div, abs_of_pos hh, div_le_one hh]
      have := abs_le.mp hy
      have h2 : |2 * y| = 2 * |y| := by rw [abs_mul]; norm_num
      rw [h2]
      linarith [abs_nonneg y]
    have h3 : |firstYieldStress σy h y| = σy * |2 * y / h| := by
      rw [firstYieldStress, abs_mul, abs_of_pos hσy]
    rw [h3]
    nlinarith [h1, hσy.le]
  · unfold fullyPlasticStress
    split <;> simp [abs_of_pos hσy]

/-- The value at the single point `y = 0` does not affect the moment. -/
example (b h σy c : ℝ) :
    sectionMoment b h (fun y => if y = 0 then c else fullyPlasticStress σy y) =
      sectionMoment b h (fullyPlasticStress σy) := by
  have hne : ∀ᵐ x : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    simp [MeasureTheory.measure_singleton]
  have hae : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      x ∈ Set.uIoc (-h / 2) (h / 2) →
        x * (b * (if x = 0 then c else fullyPlasticStress σy x)) =
          x * (b * fullyPlasticStress σy x) := by
    filter_upwards [hne] with x hx0 _
    simp [hx0]
  unfold sectionMoment
  exact intervalIntegral.integral_congr_ae hae

/-- Product forms: yield stress times the elastic modulus `b * h ^ 2 / 6` and the
plastic modulus `b * h ^ 2 / 4`. -/
example (b h σy : ℝ) (hh : 0 < h) :
    sectionMoment b h (firstYieldStress σy h) = σy * (b * h ^ 2 / 6) ∧
      sectionMoment b h (fullyPlasticStress σy) = σy * (b * h ^ 2 / 4) := by
  rw [sectionMoment_firstYieldStress, sectionMoment_fullyPlasticStress b σy hh]
  constructor <;> ring

/-- Flexure consistency: at `M = σy * b * h ^ 2 / 6` the plane-section stress
`M * y / I` with `I = b * h ^ 3 / 12` is the first-yield distribution, and its moment
is `M`. -/
example {b h σy : ℝ} (hb : b ≠ 0) (hh : h ≠ 0) :
    (fun y => (σy * b * h ^ 2 / 6) * y / (b * h ^ 3 / 12)) = firstYieldStress σy h ∧
      sectionMoment b h (fun y => (σy * b * h ^ 2 / 6) * y / (b * h ^ 3 / 12)) =
        σy * b * h ^ 2 / 6 := by
  have hfun : (fun y => (σy * b * h ^ 2 / 6) * y / (b * h ^ 3 / 12)) =
      firstYieldStress σy h := by
    funext y
    simp only [firstYieldStress]
    field_simp
    ring
  exact ⟨hfun, by rw [hfun, sectionMoment_firstYieldStress]⟩
