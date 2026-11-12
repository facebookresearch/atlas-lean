/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination

/-!
# Wind-driven gyres and vorticity balance

## i. Overview

Stipulated interior Sverdrup balance on the beta plane: `β * V = curl_z(τ) / ρ₀` with `ρ₀ > 0`, `β
  ≠ 0`, gives the meridional volume transport per width `V = curl_z(τ) / (ρ₀ * β)`. This is the
  interior balance only; it is not extended through the coastal boundary layer.

## ii. Key results

- `EarthScience.sverdrup_transport`: the balance solved for `V`.
- `EarthScience.sverdrup_zero_curl`: zero curl gives zero transport.

## iii. Table of contents

- A. Sverdrup balance

## iv. References

- `field_simp` / `linear_combination` in Mathlib (tactics).
-/

@[expose] public section

namespace EarthScience

/-- Interior Sverdrup balance: `β * V = curl / ρ₀` with `ρ₀ > 0`, `β ≠ 0`
gives `V = curl / (ρ₀ * β)`. -/
theorem sverdrup_transport {β V curl ρ₀ : ℝ} (hρ : 0 < ρ₀) (hβ : β ≠ 0)
    (h : β * V = curl / ρ₀) :
    V = curl / (ρ₀ * β) := by
  have hρ' : ρ₀ ≠ 0 := ne_of_gt hρ
  field_simp at h ⊢
  linear_combination h

set_option linter.unusedVariables false in
/-- Zero wind-stress curl gives zero interior meridional transport. -/
theorem sverdrup_zero_curl {β V ρ₀ : ℝ} (hρ : 0 < ρ₀) (hβ : β ≠ 0)
    (h : β * V = 0 / ρ₀) :
    V = 0 := by
  have h0 : β * V = 0 := by simpa using h
  exact (mul_eq_zero.mp h0).resolve_left hβ

end EarthScience
