/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.EarthScience.HydraulicJump
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conjugate-depth Froude ratio

## i. Overview

For positive conjugate depths `h1`, `h2` in a rectangular channel
satisfying the hydraulic-jump momentum identity
`q ^ 2 / g = h1 * h2 * (h1 + h2) / 2`, the depth ratio is the
positive quadratic root of the upstream squared Froude number
`Fr = q ^ 2 / (g * h1 ^ 3)`: with `r = h2 / h1`, the identity gives
`r * (1 + r) / 2 = Fr`, hence `r = (sqrt (1 + 8 * Fr) - 1) / 2`,
and `h2 > h1` exactly when `Fr > 1`.

## ii. Key results

- `EarthScience.conjugate_froude_ratio`: the depth-ratio formula
  and the supercriticality equivalence.

## iii. Table of contents

- A. Conjugate-depth Froude ratio

## iv. References

- V. T. Chow, *Open-Channel Hydraulics*, McGraw-Hill, 1959,
  Chapter 15 (hydraulic jump; conjugate depths and the upstream
  Froude number).
-/

@[expose] public section

namespace EarthScience

/-! ## A. Conjugate-depth Froude ratio -/

/-- Conjugate-depth Froude ratio law. For positive depths `h1`,
`h2` in a rectangular channel satisfying the hydraulic-jump
momentum identity `q ^ 2 / g = h1 * h2 * (h1 + h2) / 2` (unit
discharge `q`, gravity `g > 0`), the depth ratio is the positive
quadratic root `h2 / h1 = (sqrt (1 + 8 * Fr) - 1) / 2` of the
upstream squared Froude number `Fr = q ^ 2 / (g * h1 ^ 3)`, and
the downstream depth is strictly larger exactly when `Fr > 1`. -/
theorem conjugate_froude_ratio {q g h1 h2 : ℝ} (hg : 0 < g)
    (hh1 : 0 < h1) (hh2 : 0 < h2)
    (hmom : q ^ 2 / g = h1 * h2 * (h1 + h2) / 2) :
    h2 / h1 = (Real.sqrt (1 + 8 * (q ^ 2 / (g * h1 ^ 3))) - 1) / 2
      ∧ (h1 < h2 ↔ 1 < q ^ 2 / (g * h1 ^ 3)) := by
  have hg' : g ≠ 0 := ne_of_gt hg
  have hh1' : h1 ≠ 0 := ne_of_gt hh1
  have h1c : h1 ^ 3 ≠ 0 := by positivity
  have hr : (0:ℝ) < h2 / h1 := div_pos hh2 hh1
  have hq : q ^ 2 / (g * h1 ^ 3) = (q ^ 2 / g) / h1 ^ 3 := (div_div _ _ _).symm
  have hF : q ^ 2 / (g * h1 ^ 3) = (h2 / h1) * (1 + h2 / h1) / 2 := by
    rw [hq, hmom]
    field_simp
  have hsq : (2 * (h2 / h1) + 1) ^ 2 = 1 + 8 * (q ^ 2 / (g * h1 ^ 3)) := by
    rw [hF]
    ring
  have hnonneg : (0:ℝ) ≤ 2 * (h2 / h1) + 1 := by positivity
  have hsqrt : Real.sqrt (1 + 8 * (q ^ 2 / (g * h1 ^ 3)))
      = 2 * (h2 / h1) + 1 := by
    rw [← hsq, Real.sqrt_sq hnonneg]
  have hFsub : q ^ 2 / (g * h1 ^ 3) - 1
      = ((h2 / h1) - 1) * (((h2 / h1) + 2) / 2) := by
    rw [hF]
    ring
  have hmid : (0:ℝ) < ((h2 / h1) + 2) / 2 := by linarith [hr]
  refine ⟨?_, ?_⟩
  · rw [hsqrt]
    ring
  · constructor
    · intro h12
      have hr1 : (1:ℝ) < h2 / h1 := (one_lt_div hh1).mpr h12
      have hpos : (0:ℝ) < ((h2 / h1) - 1) * (((h2 / h1) + 2) / 2) :=
        mul_pos (by linarith) hmid
      rw [← hFsub] at hpos
      linarith
    · intro hF1
      rw [← one_lt_div hh1]
      by_contra hle
      have hle' : h2 / h1 ≤ 1 := not_lt.mp hle
      have hnonpos : ((h2 / h1) - 1) * (((h2 / h1) + 2) / 2) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_of_lt hmid)
      have h0 : (0:ℝ) < q ^ 2 / (g * h1 ^ 3) - 1 := by linarith
      rw [hFsub] at h0
      linarith

end EarthScience
