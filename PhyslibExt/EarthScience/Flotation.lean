/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-!
# Flotation: floating prisms and submerged fraction

For a floating prism with ice density `ρi < ρw`, the submerged fraction
is `ρi / ρw` from weight balance.

## i. Overview

A prism of thickness `H` floats with submerged depth `d`. Weight balance
`ρw * d = ρi * H` (weight of displaced water equals weight of ice, `g`
cancels) gives `d = (ρi / ρw) * H`, with `0 < d < H` and submerged
fraction `d / H = ρi / ρw`. Prism geometry, hydrostatic water, fixed
densities; grounded ice is separate. Flotation alone is not a global
sea-level response theorem.

## ii. Key results

- `EarthScience.flotation_submerged_fraction`: submerged depth, bounds,
  and fraction from weight balance.
- `EarthScience.flotation_equal_density`: equal densities give a fully
  submerged prism.

## iii. Table of contents

- A. Flotation

## iv. References

- None; proved from ordered-field algebra in Mathlib.

## A. Flotation
-/

@[expose] public section

namespace EarthScience

/-- Flotation: weight balance `ρw * d = ρi * H` gives submerged depth
`d = (ρi / ρw) * H`, with `0 < d < H` and submerged fraction `ρi / ρw`. -/
theorem flotation_submerged_fraction {ρi ρw H d : ℝ} (hρi : 0 < ρi) (hρw : ρi < ρw)
    (hH : 0 < H) (hbal : ρw * d = ρi * H) :
    d = (ρi / ρw) * H ∧ 0 < d ∧ d < H ∧ d / H = ρi / ρw := by
  have hρw_pos : 0 < ρw := lt_trans hρi hρw
  have hρw_ne : ρw ≠ 0 := ne_of_gt hρw_pos
  have hH_ne : H ≠ 0 := ne_of_gt hH
  have hd : d = (ρi / ρw) * H := by
    field_simp
    linarith
  have hfrac_pos : 0 < ρi / ρw := div_pos hρi hρw_pos
  have hd_pos : 0 < d := by
    rw [hd]
    exact mul_pos hfrac_pos hH
  have hfrac_lt : ρi / ρw < 1 := by
    rw [div_lt_one hρw_pos]
    exact hρw
  have hd_lt : d < H := by
    rw [hd]
    calc (ρi / ρw) * H < 1 * H := mul_lt_mul_of_pos_right hfrac_lt hH
      _ = H := one_mul H
  have hfrac_eq : d / H = ρi / ρw := by
    rw [hd]
    field_simp
  exact ⟨hd, hd_pos, hd_lt, hfrac_eq⟩

set_option linter.unusedVariables false in
/-- Flotation boundary: equal densities give a fully submerged prism. -/
theorem flotation_equal_density {ρ H d : ℝ} (hρ : 0 < ρ) (hH : 0 < H)
    (hbal : ρ * d = ρ * H) :
    d = H := by
  exact mul_left_cancel₀ (ne_of_gt hρ) hbal

end EarthScience
