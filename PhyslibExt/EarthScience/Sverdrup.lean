/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Wind-driven gyres and vorticity balance

## i. Overview

Stipulated interior Sverdrup balance on the beta plane: `β * V = curl_z(τ) / ρ₀` with
`ρ₀ > 0`, `β ≠ 0`, gives the meridional volume transport per width
`V = curl_z(τ) / (ρ₀ * β)`. This is the interior balance only; it is not extended through
the coastal boundary layer.

Conventions: beta-plane coordinates with `x` eastward, `y` northward and `z` upward
(right-handed). `β = ∂f/∂y` is the northward gradient of the Coriolis parameter `f`. The
surface wind stress is `τ = (τˣ, τʸ)`, and `curl` stands for the vertical component of its
curl, `curl_z(τ) = ∂τʸ/∂x - ∂τˣ/∂y`. `ρ₀ > 0` is the constant reference density, and
`V = ∫ v dz` is the depth-integrated northward velocity, i.e. the meridional volume transport
per unit zonal width, positive northward. Sverdrup (1947) writes the balance for the
meridional mass transport `M_y = ∫ ρ v dz` as `β M_y = curl_z(τ)`; with `M_y = ρ₀ V` it is
the balance `β * V = curl_z(τ) / ρ₀` stated here.

## ii. Key results

- `EarthScience.sverdrup_transport`: the balance solved for `V`.
- `EarthScience.sverdrup_zero_curl`: zero curl gives zero transport.

## iii. Table of contents

- A. Sverdrup balance

## iv. References

- H. U. Sverdrup, *Wind-driven currents in a baroclinic ocean; with application to the
  equatorial currents of the eastern Pacific*, Proc. Natl. Acad. Sci. USA 33 (1947),
  318–326: the balance `β M_y = curl_z(τ)` between the meridional mass transport and the
  wind-stress curl.
-/

@[expose] public section

namespace EarthScience

/-! ## A. Sverdrup balance -/

/-- Interior Sverdrup balance (Sverdrup 1947): `β * V = curl / ρ₀` with `ρ₀ > 0`, `β ≠ 0`
gives `V = curl / (ρ₀ * β)`. Here `curl = ∂τʸ/∂x - ∂τˣ/∂y` is the vertical curl of the
surface wind stress and `V` the northward volume transport per unit width (module
conventions). -/
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
