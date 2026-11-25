/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.MvPowerSeries.GeometricEvaluation
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Tactic.NormNum

/-! # Geometric evaluation: constants, arbitrary dimension, and a reciprocal boundary -/

open MvPowerSeries

-- A negative scalar, including the zero-dimensional case.
example (x : Fin 0 → ℝ) : geometricSum (C (-2) * (1 : MvPowerSeries (Fin 0) ℚ)) x = -2 := by
  rw [geometricSum_C_mul, geometricSum_one]
  norm_num

-- The product interface permits different bounds and radii for the two factors.
example {d : ℕ} {a b : MvPowerSeries (Fin d) ℚ} {ma mb : GeometricMajorant (Fin d)}
    {r : Fin d → ℚ≥0} (ha : IsMajorized a ma) (hb : IsMajorized b mb)
    (ia : ∀ i, (r i : ℚ) < ma.radius i) (ib : ∀ i, (r i : ℚ) < mb.radius i)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ ((r i : ℚ) : ℝ)) :
    geometricSum (a * b) x = geometricSum a x * geometricSum b x :=
  geometricSum_mul ha hb ia ib hx

private theorem eval_X (x : Fin 1 → ℝ) :
    geometricSum (X (0 : Fin 1) : MvPowerSeries (Fin 1) ℚ) x = x 0 := by
  unfold geometricSum
  rw [tsum_eq_single (Finsupp.single 0 1)]
  · simp [seriesTerm, coeff_X]
  · intro n hn
    simp [seriesTerm, coeff_X, hn]

-- X evaluates to 1 at 1 but its formal inverse is zero. Thus a nonzero
-- evaluated value alone cannot replace a nonzero constant coefficient.
example : geometricSum ((X (0 : Fin 1) : MvPowerSeries (Fin 1) ℚ)⁻¹) (fun _ => 1) ≠
    (geometricSum (X (0 : Fin 1) : MvPowerSeries (Fin 1) ℚ) (fun _ => 1))⁻¹ := by
  rw [MvPowerSeries.inv_eq_zero.mpr (by simp), eval_X]
  simp [geometricSum, seriesTerm]
