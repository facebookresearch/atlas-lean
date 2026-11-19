/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.CStarAlgebra.OperatorConvexSq

/-!
# Tests for the operator convexity of the square
-/

open scoped MatrixOrder ComplexOrder

namespace MathlibExtTest.Analysis.CStarAlgebra.OperatorConvexSq

open MathlibExt.Analysis.CStarAlgebra.OperatorConvexSq

/-- The general statement applies to complex matrices with the Loewner order. -/
example (A B : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((2⁻¹ : ℝ) • A + (1 - 2⁻¹ : ℝ) • B) * ((2⁻¹ : ℝ) • A + (1 - 2⁻¹ : ℝ) • B) ≤
      (2⁻¹ : ℝ) • (A * A) + (1 - 2⁻¹ : ℝ) • (B * B) :=
  sq_convex_comb_le hA hB (by norm_num) (by norm_num)

/-- Convexity in the sense of `ConvexOn`, for matrices. -/
example : ConvexOn ℝ {A : Matrix (Fin 3) (Fin 3) ℂ | IsSelfAdjoint A} (fun A => A * A) :=
  convexOn_mul_self

/-- Non-vacuity: for real numbers (a commutative star-ordered algebra) the inequality is the
usual convexity of `x ↦ x²`, e.g. at `x = 0`, `y = 2`, `t = 1/2`: `1 ≤ 2`. -/
example : ((2⁻¹ : ℝ) • (0 : ℝ) + (1 - 2⁻¹ : ℝ) • 2) * ((2⁻¹ : ℝ) • 0 + (1 - 2⁻¹ : ℝ) • 2) ≤
    (2⁻¹ : ℝ) • (0 * 0) + (1 - 2⁻¹ : ℝ) • (2 * 2) :=
  sq_convex_comb_le (IsSelfAdjoint.all _) (IsSelfAdjoint.all _) (by norm_num) (by norm_num)

/-- Operator monotonicity of the square fails. -/
example : ¬ ∀ A B : Matrix (Fin 2) (Fin 2) ℂ, A.PosSemidef → A ≤ B → A * A ≤ B * B := by
  obtain ⟨A, B, hA, hAB, h⟩ := not_monotone_sq
  exact fun H => h (H A B hA hAB)

end MathlibExtTest.Analysis.CStarAlgebra.OperatorConvexSq
