/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Hermite consistent load vector

## i. Overview

For a beam span `L ≠ 0` under constant load `w`, integrating the
four Hermite shape functions (in `ξ = x / L`: deflection,
rotation, deflection, rotation) against `w` over `[0, L]` gives
the consistent nodal load vector
`(w * L / 2, w * L ^ 2 / 12, w * L / 2, -w * L ^ 2 / 12)`. The
vertical entries sum to the total load `w * L`; the moment
entries are equal in magnitude and opposite in sign.

## ii. Key results

- `hermite_consistent_loads`: the four consistent-load integrals.

## iii. Table of contents

- A. Consistent loads

## iv. References

- Standard finite-element beam theory (Hermite cubic element,
  consistent load vector for uniform load).
-/

@[expose] public section

/-! ## A. Consistent loads -/

open intervalIntegral

/-- Consistent load vector for a uniform span load. For span
`L ≠ 0` and constant load `w`, integrating the four Hermite shape
functions (in `ξ = x / L`, deflections then rotations) against `w`
over `[0, L]` gives the consistent nodal load vector
`(w * L / 2, w * L ^ 2 / 12, w * L / 2, -w * L ^ 2 / 12)`: the two
vertical entries sum to the total load `w * L`, and the moment
entries are equal in magnitude and opposite in sign. -/
theorem hermite_consistent_loads {w L : ℝ} (hL : L ≠ 0) :
    (∫ x in (0 : ℝ)..L, w * (1 - 3 * (x / L) ^ 2 + 2 * (x / L) ^ 3)
      = w * L / 2)
    ∧ (∫ x in (0 : ℝ)..L,
        w * (L * ((x / L) - 2 * (x / L) ^ 2 + (x / L) ^ 3))
      = w * L ^ 2 / 12)
    ∧ (∫ x in (0 : ℝ)..L, w * (3 * (x / L) ^ 2 - 2 * (x / L) ^ 3)
      = w * L / 2)
    ∧ (∫ x in (0 : ℝ)..L,
        w * (L * (-(x / L) ^ 2 + (x / L) ^ 3))
      = -w * L ^ 2 / 12) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have heq : ∀ x : ℝ, w * (1 - 3 * (x / L) ^ 2 + 2 * (x / L) ^ 3)
        = w + (-3 * w / L ^ 2) * x ^ 2 + (2 * w / L ^ 3) * x ^ 3 := by
      intro x
      field_simp
      ring
    simp_rw [heq]
    have h1 : IntervalIntegrable (fun _ : ℝ => w) MeasureTheory.volume (0 : ℝ) L :=
      intervalIntegrable_const
    have h2 : IntervalIntegrable (fun x : ℝ => (-3 * w / L ^ 2) * x ^ 2)
        MeasureTheory.volume (0 : ℝ) L :=
      (intervalIntegrable_pow 2).const_mul _
    have h3 : IntervalIntegrable (fun x : ℝ => (2 * w / L ^ 3) * x ^ 3)
        MeasureTheory.volume (0 : ℝ) L :=
      (intervalIntegrable_pow 3).const_mul _
    have hadd : (∫ x in (0 : ℝ)..L, (w + (-3 * w / L ^ 2) * x ^ 2 + (2 * w / L ^ 3) * x ^ 3))
        = (∫ x in (0 : ℝ)..L, (w + (-3 * w / L ^ 2) * x ^ 2))
          + (∫ x in (0 : ℝ)..L, (2 * w / L ^ 3) * x ^ 3) := by
      apply integral_add
      · exact h1.add h2
      · exact h3
    rw [hadd]
    have hadd2 : (∫ x in (0 : ℝ)..L, (w + (-3 * w / L ^ 2) * x ^ 2))
        = (∫ _ in (0 : ℝ)..L, w) + (∫ x in (0 : ℝ)..L, (-3 * w / L ^ 2) * x ^ 2) := by
      apply integral_add h1 h2
    rw [hadd2]
    rw [integral_const_mul, integral_const_mul]
    rw [integral_const]
    rw [integral_pow 2, integral_pow 3]
    simp
    field_simp
    ring
  · have heq : ∀ x : ℝ, w * (L * ((x / L) - 2 * (x / L) ^ 2 + (x / L) ^ 3))
        = w * x + (-2 * w / L) * x ^ 2 + (w / L ^ 2) * x ^ 3 := by
      intro x
      field_simp
      ring
    simp_rw [heq]
    have h1 : IntervalIntegrable (fun x : ℝ => w * x) MeasureTheory.volume (0 : ℝ) L :=
      intervalIntegrable_id.const_mul _
    have h2 : IntervalIntegrable (fun x : ℝ => (-2 * w / L) * x ^ 2)
        MeasureTheory.volume (0 : ℝ) L :=
      (intervalIntegrable_pow 2).const_mul _
    have h3 : IntervalIntegrable (fun x : ℝ => (w / L ^ 2) * x ^ 3)
        MeasureTheory.volume (0 : ℝ) L :=
      (intervalIntegrable_pow 3).const_mul _
    have hadd : (∫ x in (0 : ℝ)..L, (w * x + (-2 * w / L) * x ^ 2 + (w / L ^ 2) * x ^ 3))
        = (∫ x in (0 : ℝ)..L, (w * x + (-2 * w / L) * x ^ 2))
          + (∫ x in (0 : ℝ)..L, (w / L ^ 2) * x ^ 3) := by
      apply integral_add
      · exact h1.add h2
      · exact h3
    rw [hadd]
    have hadd2 : (∫ x in (0 : ℝ)..L, (w * x + (-2 * w / L) * x ^ 2))
        = (∫ x in (0 : ℝ)..L, w * x) + (∫ x in (0 : ℝ)..L, (-2 * w / L) * x ^ 2) := by
      apply integral_add h1 h2
    rw [hadd2]
    rw [integral_const_mul, integral_const_mul, integral_const_mul]
    rw [integral_id]
    rw [integral_pow 2, integral_pow 3]
    simp
    field_simp
    ring
  · have heq : ∀ x : ℝ, w * (3 * (x / L) ^ 2 - 2 * (x / L) ^ 3)
        = (3 * w / L ^ 2) * x ^ 2 + (-2 * w / L ^ 3) * x ^ 3 := by
      intro x
      field_simp
      ring
    simp_rw [heq]
    have h2 : IntervalIntegrable (fun x : ℝ => (3 * w / L ^ 2) * x ^ 2)
        MeasureTheory.volume (0 : ℝ) L :=
      (intervalIntegrable_pow 2).const_mul _
    have h3 : IntervalIntegrable (fun x : ℝ => (-2 * w / L ^ 3) * x ^ 3)
        MeasureTheory.volume (0 : ℝ) L :=
      (intervalIntegrable_pow 3).const_mul _
    have hadd : (∫ x in (0 : ℝ)..L, ((3 * w / L ^ 2) * x ^ 2 + (-2 * w / L ^ 3) * x ^ 3))
        = (∫ x in (0 : ℝ)..L, (3 * w / L ^ 2) * x ^ 2)
          + (∫ x in (0 : ℝ)..L, (-2 * w / L ^ 3) * x ^ 3) := by
      apply integral_add h2 h3
    rw [hadd]
    rw [integral_const_mul, integral_const_mul]
    rw [integral_pow 2, integral_pow 3]
    simp
    field_simp
    ring
  · have heq : ∀ x : ℝ, w * (L * (-(x / L) ^ 2 + (x / L) ^ 3))
        = (-w / L) * x ^ 2 + (w / L ^ 2) * x ^ 3 := by
      intro x
      field_simp
    simp_rw [heq]
    have h2 : IntervalIntegrable (fun x : ℝ => (-w / L) * x ^ 2)
        MeasureTheory.volume (0 : ℝ) L :=
      (intervalIntegrable_pow 2).const_mul _
    have h3 : IntervalIntegrable (fun x : ℝ => (w / L ^ 2) * x ^ 3)
        MeasureTheory.volume (0 : ℝ) L :=
      (intervalIntegrable_pow 3).const_mul _
    have hadd : (∫ x in (0 : ℝ)..L, ((-w / L) * x ^ 2 + (w / L ^ 2) * x ^ 3))
        = (∫ x in (0 : ℝ)..L, (-w / L) * x ^ 2)
          + (∫ x in (0 : ℝ)..L, (w / L ^ 2) * x ^ 3) := by
      apply integral_add h2 h3
    rw [hadd]
    rw [integral_const_mul, integral_const_mul]
    rw [integral_pow 2, integral_pow 3]
    simp
    field_simp
    ring
