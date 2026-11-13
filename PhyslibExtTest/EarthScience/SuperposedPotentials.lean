/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.SuperposedPotentials
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Superposed-potential checks

Concrete consumers of `PhyslibExt.EarthScience.SuperposedPotentials`:
the one-dimensional potentials `Φ₁ x = 2 * x` and `Φ₂ x = 3 * x` on
`ℝ`, with gradients `2` and `3`. The superposed potential has gradient
`5`, and the superposed field is `(-2) + (-3) = -5`.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. One-dimensional concrete case

## iv. References

- `PhyslibExt.EarthScience.SuperposedPotentials`
-/

/-- Public shape of the superposition theorem. -/
example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Φ₁ Φ₂ : E → ℝ} {g₁ g₂ : E} {x : E}
    (h₁ : HasFDerivAt Φ₁ (InnerProductSpace.toDual ℝ E g₁) x)
    (h₂ : HasFDerivAt Φ₂ (InnerProductSpace.toDual ℝ E g₂) x) :
    HasFDerivAt (fun y => Φ₁ y + Φ₂ y)
      (InnerProductSpace.toDual ℝ E (g₁ + g₂)) x ∧
    -(g₁ + g₂) = (-g₁) + (-g₂) :=
  EarthScience.superposed_potentials_superpose_fields h₁ h₂

/-- Concrete case: `Φ₁ x = 2 * x`, `Φ₂ x = 3 * x` on `ℝ`. The
superposed gradient is `5` and the superposed field is `-5`. -/
example (x : ℝ) :
    HasFDerivAt (fun y : ℝ => 2 * y + 3 * y)
      (InnerProductSpace.toDual ℝ ℝ ((2 : ℝ) + 3)) x ∧
    -((2 : ℝ) + 3) = (-(2 : ℝ)) + (-(3 : ℝ)) := by
  have hgrad : ∀ (c : ℝ), HasFDerivAt (fun y : ℝ => c * y)
      (InnerProductSpace.toDual ℝ ℝ c) x := by
    intro c
    have hd : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have hf := hd.hasFDerivAt
    convert hf using 1
    apply ContinuousLinearMap.ext
    intro y
    simp [InnerProductSpace.toDual_apply_apply]
  exact EarthScience.superposed_potentials_superpose_fields
    (hgrad 2) (hgrad 3)

/-- The superposed field in the concrete case is `-5`. -/
example : -((2 : ℝ) + 3) = -(5 : ℝ) := by norm_num
