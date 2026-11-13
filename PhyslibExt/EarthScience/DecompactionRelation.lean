/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.Linarith

/-!
# Solid-volume conservation gives a decompaction relation

A layer of present thickness `h ≥ 0` and present porosity `φ ≤ φ0 < 1`
decompacts to thickness `h * (1 - φ) / (1 - φ0)`, which conserves the
solid volume `h * (1 - φ)` and is at least `h`.

## i. Overview

Under the porosity model, the solid fraction is `1 - φ`, so the solid
volume per unit area is `h * (1 - φ)`. Decompaction restores the
porosity to `φ0` while keeping the solid volume: the decompacted
thickness `h0` must satisfy `h0 * (1 - φ0) = h * (1 - φ)`, giving
`h0 = h * (1 - φ) / (1 - φ0)`. Since `φ ≤ φ0 < 1`, the ratio
`(1 - φ) / (1 - φ0)` is at least `1`, so `h0 ≥ h`: decompaction
thickens the layer. This is the algebraic decompaction relation; it
is distinct from the parent no-compaction sediment-age model in
`PhyslibExt.EarthScience.SedimentAges`, which has no porosity at all.

## ii. Key results

- `EarthScience.decompaction_relation`: solid-volume conservation
  and `h ≤ h0` for the decompacted thickness.

## iii. References

- `div_mul_cancel₀`, `le_div_iff₀`, `le_mul_of_one_le_right`
  (Mathlib).
-/

@[expose] public section

namespace EarthScience

/-- Solid-volume conservation gives a decompaction relation under its
porosity model: a layer of present thickness `h ≥ 0` and present
porosity `φ ≤ φ0 < 1` decompacts to thickness
`h * (1 - φ) / (1 - φ0)`, which conserves the solid volume
`h * (1 - φ)` and is at least `h`. -/
theorem decompaction_relation {h φ φ0 : ℝ} (hh : 0 ≤ h) (hφ : φ ≤ φ0)
    (hφ0 : φ0 < 1) :
    (h * (1 - φ) / (1 - φ0)) * (1 - φ0) = h * (1 - φ)
      ∧ h ≤ h * (1 - φ) / (1 - φ0) := by
  have hpos : (0 : ℝ) < 1 - φ0 := by linarith
  have hne : (1 : ℝ) - φ0 ≠ 0 := ne_of_gt hpos
  refine ⟨?_, ?_⟩
  · exact div_mul_cancel₀ _ hne
  · have h1 : (1 : ℝ) ≤ (1 - φ) / (1 - φ0) := by
      rw [le_div_iff₀ hpos, one_mul]
      linarith
    rw [mul_div_assoc]
    exact le_mul_of_one_le_right hh h1

end EarthScience
