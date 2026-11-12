/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.EkmanLayers

/-!
# Ekman-layer checks

Concrete consumers of `PhyslibExt.EarthScience.EkmanLayers`: the
Ekman balance for `τ = (1, 2, 0)`, `ρ₀ = 2`, `f = 3`, perpendicularity
there, the zero-stress case, and the southern-hemisphere sign flip
(`f = -3`).

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`τ = (1, 2, 0)`, `ρ₀ f = 6`, `M = (1/3, -1/6, 0)` and
`ρ₀ f (k̂ × M) = (1, 2, 0) = τ`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Ekman balance at `τ = (1, 2, 0)`
- B. Zero stress and the sign flip

## iv. References

- `PhyslibExt.EarthScience.EkmanLayers`
-/

/-- Ekman balance for `τ = (1, 2, 0)`, `ρ₀ = 2`, `f = 3`. -/
example : ((2 : ℝ) * 3) • ![(1 : ℝ) / (2 * 3), 2 / (2 * 3), 0] = ![1, 2, (0 : ℝ)] :=
  EarthScience.ekman_transport 2 3 (by norm_num) (by norm_num) ![1, 2, 0] (by simp)

/-- Perpendicularity for the same parameters. -/
example : (![2 / (2 * 3), -(1 / (2 * 3)), (0 : ℝ)] : Fin 3 → ℝ) ⬝ᵥ ![1, 2, 0] = 0 ∧
    (![2 / (2 * 3), -(1 / (2 * 3)), (0 : ℝ)] : Fin 3 → ℝ) 2 = 0 := by
  have h := EarthScience.ekman_transport_perp 2 3 (by norm_num) (by norm_num) ![1, 2, 0]
  simpa using h

/-- Zero stress: the balance is `0 = 0`. -/
example : ((2 : ℝ) * 3) • ![(0 : ℝ) / (2 * 3), 0 / (2 * 3), 0] = ![0, 0, (0 : ℝ)] :=
  EarthScience.ekman_transport 2 3 (by norm_num) (by norm_num) ![0, 0, 0] (by simp)

/-- Southern hemisphere: with `f = -3` the same balance holds. -/
example : ((2 : ℝ) * (-3)) • ![(1 : ℝ) / (2 * (-3)), 2 / (2 * (-3)), 0] = ![1, 2, (0 : ℝ)] :=
  EarthScience.ekman_transport 2 (-3) (by norm_num) (by norm_num) ![1, 2, 0] (by simp)
