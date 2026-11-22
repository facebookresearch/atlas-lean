/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

import PhyslibExt.EarthScience.Geotechnical.InfiniteSlope

/-!
# Infinite-slope checks

Focused checks for `PhyslibExt.EarthScience.Geotechnical.InfiniteSlope`:
at `beta = π / 4` with unit weight `2` and vertical depth `3`, both the
normal and driving stresses are `3`; the slab volume for area `5` is
`15 * cos (π / 4)`; and the tan-ratio theorem applies at that angle.

These are elaboration and non-vacuity checks, not new results.
-/

open EarthScience

/-- At `π / 4` the normal and driving stresses agree. -/
example : infiniteSlopeNormalStress 2 3 (Real.pi / 4) = 3
    ∧ infiniteSlopeDrivingStress 2 3 (Real.pi / 4) = 3 := by
  constructor <;>
    simp only [infiniteSlopeNormalStress, infiniteSlopeDrivingStress,
      Real.cos_pi_div_four, Real.sin_pi_div_four] <;> ring_nf <;>
    linarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]

/-- Slab volume at the same witness. -/
example : infiniteSlopeSlabVolume 5 3 (Real.pi / 4)
    = 15 * Real.cos (Real.pi / 4) := by
  norm_num [infiniteSlopeSlabVolume]

/-- The tan-ratio identity at `π / 4`, through the public theorem. -/
example : infiniteSlopeDrivingStress 2 3 (Real.pi / 4)
    = infiniteSlopeNormalStress 2 3 (Real.pi / 4) * Real.tan (Real.pi / 4) :=
  infiniteSlopeDriving_eq_normal_mul_tan (by positivity) (by
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith [Real.pi_pos])
