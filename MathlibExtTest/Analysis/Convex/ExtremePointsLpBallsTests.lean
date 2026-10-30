/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.ExtremePointsLpBalls
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for extreme points of the unit balls of finite `ℓ¹` and `ℓ^∞` spaces
-/

@[expose] public section

open Set Metric
open scoped ENNReal

namespace MathlibExt.Analysis.Convex.ExtremePointsLpBallsTests

open MathlibExt.Analysis.Convex.ExtremePointsLpBalls

/-- The `RCLike` strict-convexity instance is available for `ℂ`. -/
example : StrictConvexSpace ℝ ℂ := inferInstance

/-- The `RCLike` strict-convexity instance is available for `ℝ`. -/
example : StrictConvexSpace ℝ ℝ := inferInstance

/-- In `ℓ^∞` on `Fin 2`, the vector `(1, -1)` is an extreme point of the
closed unit ball. -/
example : (WithLp.toLp (∞ : ℝ≥0∞) ![1, -1] : PiLp ∞ fun _ : Fin 2 => ℝ) ∈
    (Metric.closedBall (0 : PiLp ∞ fun _ : Fin 2 => ℝ) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_piLp_top]
  intro i
  fin_cases i <;> simp

/-- In `ℓ^∞` on `Fin 2`, the vector `(1, 1/2)` is not an extreme point of
the closed unit ball, since its second coordinate has norm `< 1`. -/
example : (WithLp.toLp (∞ : ℝ≥0∞) ![1, 1 / 2] : PiLp ∞ fun _ : Fin 2 => ℝ) ∉
    (Metric.closedBall (0 : PiLp ∞ fun _ : Fin 2 => ℝ) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_piLp_top]
  intro h
  have h1 : ‖(WithLp.toLp (∞ : ℝ≥0∞) ![1, 1 / 2] : PiLp ∞ fun _ : Fin 2 => ℝ) 1‖ = 1 :=
    h 1
  simp only [Matrix.cons_val_one] at h1
  norm_num at h1

/-- In `ℓ^∞` on `Fin 2` over `ℂ`, the vector `(1, -I)` is an extreme point
of the closed unit ball. -/
example : (WithLp.toLp (∞ : ℝ≥0∞) ![1, -Complex.I] : PiLp ∞ fun _ : Fin 2 => ℂ) ∈
    (Metric.closedBall (0 : PiLp ∞ fun _ : Fin 2 => ℂ) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_piLp_top]
  intro i
  fin_cases i <;> simp

/-- In `ℓ¹` on `Fin 2`, the coordinate vector `e₀` is an extreme point of
the closed unit ball. -/
example : (PiLp.single 1 (0 : Fin 2) (1 : ℝ)) ∈
    (Metric.closedBall (0 : PiLp 1 fun _ : Fin 2 => ℝ) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_piLp_one]
  exact ⟨0, 1, norm_one, rfl⟩

/-- In `ℓ¹` on `Fin 2` over `ℂ`, the vector `I • e₀` is an extreme point of
the closed unit ball: the scalar has norm `1`. -/
example : (PiLp.single 1 (0 : Fin 2) (Complex.I : ℂ)) ∈
    (Metric.closedBall (0 : PiLp 1 fun _ : Fin 2 => ℂ) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_piLp_one]
  exact ⟨0, Complex.I, Complex.norm_I, rfl⟩

/-- In `ℓ¹` on `Fin 2`, the vector `(1/2, 1/2)` is not an extreme point of
the closed unit ball: it has two nonzero coordinates. -/
example : (WithLp.toLp (1 : ℝ≥0∞) ![1 / 2, 1 / 2] : PiLp 1 fun _ : Fin 2 => ℝ) ∉
    (Metric.closedBall (0 : PiLp 1 fun _ : Fin 2 => ℝ) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_piLp_one]
  rintro ⟨i, c, hc, hxi⟩
  fin_cases i
  · have h1 := congrArg (fun w : PiLp 1 fun _ : Fin 2 => ℝ => w 1) hxi
    simp only [Matrix.cons_val_one, PiLp.single_apply] at h1
    norm_num at h1
  · have h0 := congrArg (fun w : PiLp 1 fun _ : Fin 2 => ℝ => w 0) hxi
    simp only [Matrix.cons_val_zero, PiLp.single_apply] at h0
    norm_num at h0

/-- In `ℓ¹` on `Fin 3`, the vector `2 • e₁` is not an extreme point of the
closed unit ball: the scalar has norm `2`, not `1`. -/
example : (PiLp.single 1 (1 : Fin 3) (2 : ℝ)) ∉
    (Metric.closedBall (0 : PiLp 1 fun _ : Fin 3 => ℝ) 1).extremePoints ℝ := by
  rw [extremePoints_closedBall_piLp_one]
  rintro ⟨i, c, hc, hxi⟩
  have h1 := congrArg (fun w : PiLp 1 fun _ : Fin 3 => ℝ => w 1) hxi
  by_cases hi : (1 : Fin 3) = i
  · subst hi
    simp only [PiLp.single_eq_same] at h1
    rw [← h1] at hc
    norm_num at hc
  · rw [PiLp.single_eq_same (β := fun _ : Fin 3 => ℝ) 1 1 (2 : ℝ),
      PiLp.single_eq_of_ne' (β := fun _ : Fin 3 => ℝ) 1 (Ne.symm hi) c] at h1
    norm_num at h1

end MathlibExt.Analysis.Convex.ExtremePointsLpBallsTests
