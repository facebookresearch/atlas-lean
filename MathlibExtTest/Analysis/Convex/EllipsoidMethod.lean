/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.EllipsoidMethod
public import Mathlib.Algebra.Order.Star.Real

@[expose] public section

open MathlibExt.Analysis.Convex.EllipsoidMethod

/-! Non-vacuity checks for the volume lemma and the determinant update. -/

example : volumeRatio 2 < Real.exp (-1 / 6) := by
  have := volumeRatio_lt_exp (n := 2) le_rfl
  norm_num at this ⊢
  exact this

example : 0 < volumeRatio 3 := volumeRatio_pos (by norm_num)

example : volumeRatio 2 ^ 12 < Real.exp (-2) := by
  have := volumeRatio_pow_lt_exp (n := 2) (k := 12) le_rfl (by norm_num)
  norm_num at this ⊢
  exact this

/-- The hypotheses of `det_nextMatrix` are satisfiable: the identity matrix and a basis vector. -/
example : (nextMatrix (1 : Matrix (Fin 2) (Fin 2) ℝ) (Pi.single 0 1)).det =
    ((2 : ℝ) ^ 2 / ((2 : ℝ) ^ 2 - 1)) ^ 2 * ((2 - 1) / (2 + 1)) * 1 := by
  have h := det_nextMatrix (n := 2) Matrix.PosDef.one (c := Pi.single 0 1)
    (by intro h; simpa using congrFun h 0)
  simpa using h

example : Real.sqrt (((2 : ℝ) ^ 2 / ((2 : ℝ) ^ 2 - 1)) ^ 2 * ((2 - 1) / (2 + 1))) =
    volumeRatio 2 := by
  simpa using sqrt_detRatio_eq_volumeRatio (n := 2) le_rfl

/-- The containment applies to the unit disc and the cut `x₀ ≤ 0`. -/
example : ellipsoid 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) ∩
    {x | (Pi.single 0 1 : Fin 2 → ℝ) ⬝ᵥ x ≤ (Pi.single 0 1 : Fin 2 → ℝ) ⬝ᵥ 0} ⊆
    ellipsoid (nextCenter 0 1 (Pi.single 0 1)) (nextMatrix 1 (Pi.single 0 1)) :=
  halfEllipsoid_subset_nextEllipsoid le_rfl Matrix.PosDef.one 0
    (by intro h; simpa using congrFun h 0)

/-- The centre of the unit disc lies in the half-disc, so the hypotheses are jointly satisfiable. -/
example : (0 : Fin 2 → ℝ) ∈ ellipsoid 0 (1 : Matrix (Fin 2) (Fin 2) ℝ) ∩
    {x | (Pi.single 0 1 : Fin 2 → ℝ) ⬝ᵥ x ≤ (Pi.single 0 1 : Fin 2 → ℝ) ⬝ᵥ 0} := by
  simp [ellipsoid]
