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

A layer of present thickness `h ≥ 0` and present porosity `φ`, with
`0 ≤ φ ≤ φ0 < 1`, decompacts to thickness `h * (1 - φ) / (1 - φ0)`,
which conserves the solid volume `h * (1 - φ)` and is at least `h`.

## i. Overview

Under the porosity model, the solid fraction is `1 - φ`, so the solid
volume per unit area is `h * (1 - φ)`. Decompaction restores the
porosity to `φ0` while keeping the solid volume: the decompacted
thickness `h0` must satisfy `h0 * (1 - φ0) = h * (1 - φ)`, giving
`h0 = h * (1 - φ) / (1 - φ0)`. Since `φ ≤ φ0 < 1`, the ratio
`(1 - φ) / (1 - φ0)` is at least `1`, so `h0 ≥ h`: decompaction
thickens the layer. The algebra holds for all reals with `0 ≤ h` and
`φ ≤ φ0 < 1`; the physical statement also assumes the porosity lower
bound `0 ≤ φ` (hence `0 ≤ φ0`), which the proof does not use. This is
distinct from the parent no-compaction sediment-age model in
`PhyslibExt.EarthScience.SedimentAges`, which has no porosity at all.

## ii. Key results

- `EarthScience.mul_one_sub_div_one_sub_mul_eq_and_le`: the unrestricted
  algebraic identity and bound, for all reals with `0 ≤ h` and
  `φ ≤ φ0 < 1`.
- `EarthScience.decompaction_relation`: for porosities
  `0 ≤ φ ≤ φ0 < 1`, solid-volume conservation and `h ≤ h0` for the
  decompacted thickness.

## iii. References

- `div_mul_cancel₀`, `le_div_iff₀`, `le_mul_of_one_le_right`
  (Mathlib).
-/

@[expose] public section

namespace EarthScience

/-- Unrestricted algebraic identity and bound behind the decompaction
relation: for all reals with `0 ≤ h` and `φ ≤ φ0 < 1`,
`h * (1 - φ) / (1 - φ0)` times `1 - φ0` is `h * (1 - φ)`, and
`h ≤ h * (1 - φ) / (1 - φ0)`. No porosity range is assumed, so this is
not a physical statement by itself; for porosities `0 ≤ φ ≤ φ0 < 1` see
`decompaction_relation`. -/
lemma mul_one_sub_div_one_sub_mul_eq_and_le {h φ φ0 : ℝ} (hh : 0 ≤ h) (hφ : φ ≤ φ0)
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

/-- Solid-volume conservation gives a decompaction relation: a layer of
present thickness `h ≥ 0` and present porosity `φ`, with
`0 ≤ φ ≤ φ0 < 1`, decompacted to porosity `φ0`, has thickness
`h * (1 - φ) / (1 - φ0)`, which conserves the solid volume
`h * (1 - φ)` and is at least `h`. The lower bound `0 ≤ φ` (hence
`0 ≤ φ0`) restricts to physical porosities; the proof does not use it
(see `mul_one_sub_div_one_sub_mul_eq_and_le`). -/
theorem decompaction_relation {h φ φ0 : ℝ} (hh : 0 ≤ h) (_hφ_nonneg : 0 ≤ φ) (hφ : φ ≤ φ0)
    (hφ0 : φ0 < 1) :
    (h * (1 - φ) / (1 - φ0)) * (1 - φ0) = h * (1 - φ)
      ∧ h ≤ h * (1 - φ) / (1 - φ0) :=
  mul_one_sub_div_one_sub_mul_eq_and_le hh hφ hφ0

end EarthScience
