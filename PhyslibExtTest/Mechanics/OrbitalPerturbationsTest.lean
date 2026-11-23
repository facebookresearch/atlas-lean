/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.InnerProductSpace.PiL2
import PhyslibExt.Mechanics.OrbitalPerturbations

/-!
# Inverse-square exterior Lipschitz checks

Concrete consumers of `PhyslibExt.Mechanics.OrbitalPerturbations` in
three-dimensional Euclidean space: opposite boundary points of the
excluded ball and the field magnitude there.

## i. Overview

These are elaboration and non-vacuity checks, not new results.

## ii. Key results

No new definitions or results are introduced here.

## iii. Table of contents

- A. Opposite boundary points in `EuclideanSpace ℝ (Fin 3)`

## iv. References

- `PhyslibExt.Mechanics.OrbitalPerturbations`
-/

/-- Opposite boundary points `r = (2, 0, 0)`, `s = -r` of the excluded
ball of radius `2`, at `μ = 5`: the exterior Lipschitz bound applies
with constant `4 * 5 / 2^3`. -/
example :
    let r : EuclideanSpace ℝ (Fin 3) := EuclideanSpace.single 0 2
    ‖OrbitalPerturbations.inverseSquareField 5 r -
        OrbitalPerturbations.inverseSquareField 5 (-r)‖ ≤
      (4 * 5 / 2 ^ 3) * ‖r - -r‖ := by
  intro r
  have hr : ‖r‖ = 2 := by simp [r, PiLp.norm_single]
  have hsr : ‖(-r : EuclideanSpace ℝ (Fin 3))‖ = 2 := by simp [hr]
  exact OrbitalPerturbations.inverseSquareField_lipschitz_exterior
    (by norm_num) (by norm_num) hr.ge hsr.ge

/-- Field magnitude at the same boundary point: `5 / 2^2`. -/
example :
    ‖OrbitalPerturbations.inverseSquareField 5
      (EuclideanSpace.single (0 : Fin 3) (2 : ℝ))‖ = 5 / 4 := by
  have hnr : ‖EuclideanSpace.single (0 : Fin 3) (2 : ℝ)‖ = 2 := by
    simp [PiLp.norm_single]
  have hne : (EuclideanSpace.single (0 : Fin 3) (2 : ℝ)) ≠ 0 := by
    intro h
    rw [h] at hnr
    simp at hnr
  rw [OrbitalPerturbations.norm_inverseSquareField (by norm_num) hne]
  norm_num [PiLp.norm_single]

/-- The bundled `LipschitzOnWith` form on the exterior set at
`μ = 5`, `rmin = 2`. -/
example :
    LipschitzOnWith ⟨4 * 5 / 2 ^ 3, by positivity⟩
      (OrbitalPerturbations.inverseSquareField 5)
      {r : EuclideanSpace ℝ (Fin 3) | 2 ≤ ‖r‖} :=
  OrbitalPerturbations.inverseSquareField_lipschitzOnWith
    (by norm_num) (by norm_num)

/-- Direction check: at `r = (2, 0, 0)` with `μ = 5` the field is the
outward scalar multiple `(5 / 8) • r` (parallel to `r`, not toward the
origin). -/
example :
    OrbitalPerturbations.inverseSquareField 5
        (EuclideanSpace.single (0 : Fin 3) (2 : ℝ)) =
      (5 / 8 : ℝ) • EuclideanSpace.single (0 : Fin 3) (2 : ℝ) := by
  have hnr : ‖EuclideanSpace.single (0 : Fin 3) (2 : ℝ)‖ = 2 := by
    simp [PiLp.norm_single]
  have h58 : (5 : ℝ) / 2 ^ 3 = 5 / 8 := by norm_num
  simp [OrbitalPerturbations.inverseSquareField, hnr, h58]

/-- Zero-parameter endpoint: the bundled Lipschitz form at `μ = 0`. -/
example :
    LipschitzOnWith ⟨4 * 0 / 2 ^ 3, by positivity⟩
      (OrbitalPerturbations.inverseSquareField 0)
      {r : EuclideanSpace ℝ (Fin 3) | 2 ≤ ‖r‖} :=
  OrbitalPerturbations.inverseSquareField_lipschitzOnWith
    (le_refl 0) (by norm_num)

/-- J2 envelope at the pole point `r = (0, 0, 2)` with `μ = 3`,
`R = 1`, `J2 = 1 / 2`, `rmin = 2`: the bound is `9 / 32`, and the
normalized polynomial at `u = 1` equals `4`. -/
example :
    ‖OrbitalPerturbations.j2Accel 3 1 (1 / 2)
        (EuclideanSpace.single (2 : Fin 3) (2 : ℝ))‖ ≤
      3 * |(1 : ℝ) / 2| * 3 * 1 ^ 2 / 2 ^ 4 ∧
        (5 : ℝ) * 1 ^ 2 - 2 * 1 + 1 = 4 := by
  constructor
  · apply OrbitalPerturbations.j2Accel_norm_le (by norm_num) (by norm_num)
    simp [PiLp.norm_single]
  · norm_num
