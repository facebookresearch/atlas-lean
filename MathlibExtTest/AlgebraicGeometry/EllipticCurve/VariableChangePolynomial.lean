/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.VariableChangePolynomial
import Mathlib.Tactic.NormNum

@[expose] public section

open Polynomial

open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine

/-- The curve `y² = x³ - x` over `ℚ`, whose discriminant is `64`. -/
private noncomputable abbrev testCurve : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩

private lemma testCurve_Δ : testCurve.Δ = 64 := by
  simp only [Δ, b₂, b₄, b₆, b₈]
  norm_num

/-- For `y² = x³ - x`, the partial derivatives `2y` and `3x² - 1` generate the unit ideal of
the coordinate ring. -/
example : ∃ p q : testCurve.toAffine.CoordinateRing,
    p * AdjoinRoot.mk testCurve.toAffine.polynomial testCurve.toAffine.polynomialY +
      q * AdjoinRoot.mk testCurve.toAffine.polynomial (-testCurve.toAffine.polynomialX) = 1 :=
  CoordinateRing.exists_mul_add_mul_eq_one_of_Δ_ne_zero testCurve (by rw [testCurve_Δ]; norm_num)

/-- The translation `(u, r, s, t) = (1, 1, 0, 0)` multiplies the polynomial by `u⁶ = 1`. -/
example (W : WeierstrassCurve ℚ) :
    (W.map (Polynomial.C.comp Polynomial.C)).toAffine.polynomial.evalEval
        (CC (((⟨1, 1, 0, 0⟩ : VariableChange ℚ).u : ℚ) ^ 2) * Polynomial.C Polynomial.X + CC 1)
        (CC (((⟨1, 1, 0, 0⟩ : VariableChange ℚ).u : ℚ) ^ 3) * Y +
          CC (((⟨1, 1, 0, 0⟩ : VariableChange ℚ).u : ℚ) ^ 2 * 0) * Polynomial.C Polynomial.X +
          CC 0) =
      CC (((⟨1, 1, 0, 0⟩ : VariableChange ℚ).u : ℚ) ^ 6) *
        ((⟨1, 1, 0, 0⟩ : VariableChange ℚ) • W).toAffine.polynomial :=
  evalEval_polynomial_variableChange W ⟨1, 1, 0, 0⟩

example (W : WeierstrassCurve ℚ) (C : VariableChange ℚ) :
    (W.map (Polynomial.C.comp Polynomial.C)).toAffine.polynomialY.evalEval
        (CC ((C.u : ℚ) ^ 2) * Polynomial.C Polynomial.X + CC C.r)
        (CC ((C.u : ℚ) ^ 3) * Y + CC ((C.u : ℚ) ^ 2 * C.s) * Polynomial.C Polynomial.X + CC C.t) =
      CC ((C.u : ℚ) ^ 3) * (C • W).toAffine.polynomialY :=
  (evalEval_partials_variableChange W C).1

end WeierstrassCurve.Affine
