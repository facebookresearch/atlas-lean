/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.EllipsoidVolume

@[expose] public section

open MathlibExt.Analysis.Convex.EllipsoidMethod MeasureTheory

/-! Non-vacuity: the volume lemma applied to the unit disc and the cut `x₀ ≤ 0`. -/

example : volume (ellipsoid (nextCenter (0 : Fin 2 → ℝ) 1 (Pi.single 0 1))
    (nextMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) (Pi.single 0 1))) <
    ENNReal.ofReal (Real.exp (-1 / (2 * ((2 : ℕ) + 1 : ℝ)))) *
      volume (ellipsoid (0 : Fin 2 → ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)) :=
  volume_nextEllipsoid_lt le_rfl Matrix.PosDef.one 0 (by intro h; simpa using congrFun h 0)

/-- Scaling the identity by `4` doubles the radius, so the volume of the disc is multiplied by
`√(det (4 I)) = 4`. -/
example : volume (ellipsoid (0 : Fin 2 → ℝ) ((4 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ))) =
    ENNReal.ofReal 4 * volume (ellipsoid (0 : Fin 2 → ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
  rw [volume_ellipsoid (Matrix.PosDef.one.smul (by norm_num : (0 : ℝ) < 4))]
  congr 2
  rw [Matrix.det_smul, Matrix.det_one]
  norm_num
  rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

example : 0 < volume (ellipsoid (0 : Fin 3 → ℝ) (1 : Matrix (Fin 3) (Fin 3) ℝ)) :=
  volume_unitEllipsoid_pos
