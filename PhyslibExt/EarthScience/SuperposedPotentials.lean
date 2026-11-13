/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Superposed potentials superpose fields

## i. Overview

If two potentials `Φ₁, Φ₂` have gradients `g₁, g₂` at a point `x`,
then the superposed potential `Φ₁ + Φ₂` has gradient `g₁ + g₂` at
`x`, and the field `-(g₁ + g₂)` (the negative gradient) is the sum
`(-g₁) + (-g₂)` of the individual fields. The gradient is phrased with
`InnerProductSpace.toDual`, which is additive, so the first claim is
the additivity of the Fréchet derivative and the second is `neg_add`.

## ii. Key results

- `EarthScience.superposed_potentials_superpose_fields`: gradients and
  fields of a sum of potentials are the sums of the gradients and fields.

## iii. Table of contents

- A. Superposition of potentials and fields

## iv. References

- `HasFDerivAt.add` in Mathlib (additivity of the derivative).
- `map_add` for the linear equiv `InnerProductSpace.toDual`.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Superposition of potentials and fields -/

/-- Superposed potentials superpose fields: if `Φ₁, Φ₂` have gradients
`g₁, g₂` at `x`, then `Φ₁ + Φ₂` has gradient `g₁ + g₂` at `x`, and the
field `-(g₁ + g₂)` (negative gradient) is the sum `(-g₁) + (-g₂)` of
the individual fields. -/
theorem superposed_potentials_superpose_fields
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {Φ₁ Φ₂ : E → ℝ} {g₁ g₂ : E} {x : E}
    (h₁ : HasFDerivAt Φ₁ (InnerProductSpace.toDual ℝ E g₁) x)
    (h₂ : HasFDerivAt Φ₂ (InnerProductSpace.toDual ℝ E g₂) x) :
    HasFDerivAt (fun y => Φ₁ y + Φ₂ y)
      (InnerProductSpace.toDual ℝ E (g₁ + g₂)) x ∧
    -(g₁ + g₂) = (-g₁) + (-g₂) := by
  constructor
  · have h := h₁.add h₂
    have heq : (InnerProductSpace.toDual ℝ E) (g₁ + g₂)
        = (InnerProductSpace.toDual ℝ E) g₁ + (InnerProductSpace.toDual ℝ E) g₂ :=
      map_add _ _ _
    rwa [← heq] at h
  · exact neg_add g₁ g₂

end EarthScience
