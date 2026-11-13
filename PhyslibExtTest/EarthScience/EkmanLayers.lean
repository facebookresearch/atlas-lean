/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.EkmanLayers
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Ekman-layer checks

Concrete consumers of `PhyslibExt.EarthScience.EkmanLayers`: the
transport and the cross product for `τ = (1, 2, 0)`, `ρ₀ = 2`, `f = 3`,
the Ekman balance and perpendicularity there, the zero-stress case, the
northern-hemisphere direction, the southern-hemisphere sign flip
(`f = -3`), and the need for `τ 2 = 0`.

## i. Overview

These are elaboration and non-vacuity checks, not new results. With
`τ = (1, 2, 0)`, `ρ₀ f = 6`, `M = (1/3, -1/6, 0)`,
`k̂ ⨯₃ M = (1/6, 1/3, 0)` and `ρ₀ f (k̂ ⨯₃ M) = (1, 2, 0) = τ`.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Ekman balance at `τ = (1, 2, 0)`
- B. Zero stress, direction, the sign flip, and vertical stress

## iv. References

- `PhyslibExt.EarthScience.EkmanLayers`
-/

open Matrix

/-- The transport for `τ = (1, 2, 0)`, `ρ₀ = 2`, `f = 3` is `(1/3, -1/6, 0)`. -/
example : EarthScience.ekmanTransport 2 3 ![1, 2, 0] = ![1 / 3, -(1 / 6), 0] := by
  ext i
  fin_cases i <;> norm_num [EarthScience.ekmanTransport]

/-- Mathlib's cross product evaluates `k̂ ⨯₃ (1/3, -1/6, 0) = (1/6, 1/3, 0)`. -/
example : (![0, 0, 1] : Fin 3 → ℝ) ⨯₃ ![1 / 3, -(1 / 6), 0] = ![1 / 6, 1 / 3, 0] := by
  ext i
  fin_cases i <;> simp [cross_apply]

/-- Ekman balance for `τ = (1, 2, 0)`, `ρ₀ = 2`, `f = 3`. -/
example : ((2 : ℝ) * 3) •
    ((![0, 0, 1] : Fin 3 → ℝ) ⨯₃ EarthScience.ekmanTransport 2 3 ![1, 2, 0]) =
      ![1, 2, 0] :=
  EarthScience.ekman_transport 2 3 (by norm_num) (by norm_num) ![1, 2, 0] (by simp)

/-- Perpendicularity for the same parameters. -/
example : EarthScience.ekmanTransport 2 3 ![1, 2, 0] ⬝ᵥ ![1, 2, 0] = 0 ∧
    EarthScience.ekmanTransport 2 3 ![1, 2, 0] 2 = 0 :=
  EarthScience.ekman_transport_perp 2 3 (by norm_num) (by norm_num) ![1, 2, 0]

/-- Zero stress gives zero transport. -/
example : EarthScience.ekmanTransport 2 3 0 = 0 := by
  ext i
  fin_cases i <;> simp [EarthScience.ekmanTransport]

/-- Northern hemisphere (`f > 0`): an eastward stress `(1, 0, 0)` drives a
southward transport, to the right of the wind. -/
example : EarthScience.ekmanTransport 2 3 ![1, 0, 0] = ![0, -(1 / 6), 0] := by
  ext i
  fin_cases i <;> norm_num [EarthScience.ekmanTransport]

/-- Southern hemisphere: with `f = -3` the transport flips sign and the same
balance holds. -/
example : EarthScience.ekmanTransport 2 (-3) ![1, 2, 0] =
    -EarthScience.ekmanTransport 2 3 ![1, 2, 0] := by
  ext i
  fin_cases i <;> norm_num [EarthScience.ekmanTransport]

example : ((2 : ℝ) * (-3)) •
    ((![0, 0, 1] : Fin 3 → ℝ) ⨯₃ EarthScience.ekmanTransport 2 (-3) ![1, 2, 0]) =
      ![1, 2, 0] :=
  EarthScience.ekman_transport 2 (-3) (by norm_num) (by norm_num) ![1, 2, 0] (by simp)

/-- `τ 2 = 0` is needed: the horizontal transport cannot balance a vertical
stress component. -/
example : ((2 : ℝ) * 3) •
    ((![0, 0, 1] : Fin 3 → ℝ) ⨯₃ EarthScience.ekmanTransport 2 3 ![1, 2, 5]) ≠
      ![1, 2, 5] := by
  intro h
  have h2 := congrFun h 2
  simp [EarthScience.ekmanTransport, cross_apply] at h2
