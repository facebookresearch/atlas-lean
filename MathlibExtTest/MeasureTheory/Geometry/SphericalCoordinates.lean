/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.MeasureTheory.Geometry.SphericalCoordinates
import Mathlib.Tactic.Ring

open Real MeasureTheory MathlibExt.MeasureTheory.Geometry.SphericalCoordinatesWanted

private theorem radius_sq (r θ φ : ℝ) :
    (r * sin φ * cos θ) ^ 2 + (r * sin φ * sin θ) ^ 2 + (r * cos φ) ^ 2 = r ^ 2 := by
  calc
    _ = r ^ 2 * (sin φ ^ 2 * (sin θ ^ 2 + cos θ ^ 2) + cos φ ^ 2) := by ring
    _ = r ^ 2 := by rw [sin_sq_add_cos_sq, mul_one, sin_sq_add_cos_sq, mul_one]

private noncomputable def unitBallIndicator (p : ℝ × ℝ × ℝ) : ℝ :=
  if p.1 ^ 2 + p.2.1 ^ 2 + p.2.2 ^ 2 < 1 then 1 else 0

-- The unit ball pulls back to the radial cutoff `r² < 1`, independently of both angles.
example :
    (∫ p in {p : ℝ × ℝ × ℝ |
      0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 < 2 * π ∧ 0 < p.2.2 ∧ p.2.2 < π},
      (p.1 ^ 2 * sin p.2.2 : ℝ) • (if p.1 ^ 2 < 1 then (1 : ℝ) else 0)) =
      ∫ p, unitBallIndicator p := by
  have h := integral_comp_spherical_symm unitBallIndicator
  simp only [unitBallIndicator, radius_sq] at h ⊢
  exact h
