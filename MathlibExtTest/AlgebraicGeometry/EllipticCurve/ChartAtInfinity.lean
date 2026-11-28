/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.ChartAtInfinity

/-!
# Tests for the two affine charts of a projective Weierstrass cubic

Examples on the curve `y² + y = x³ - x` over `ℚ`.
-/

@[expose] public section

namespace WeierstrassCurve.ChartAtInfinityTest

open WeierstrassCurve.Projective

/-- The curve `y² + y = x³ - x` over `ℚ`. -/
abbrev E : WeierstrassCurve ℚ := { a₁ := 0, a₂ := 0, a₃ := 1, a₄ := -1, a₆ := 0 }

/-- Its polynomial at infinity is `w + w² - z³ + z w²`. -/
example : E.polynomialAtInfinity =
    MvPolynomial.X 1 + MvPolynomial.X 1 ^ 2 - MvPolynomial.X 0 ^ 3 +
      MvPolynomial.X 0 * MvPolynomial.X 1 ^ 2 := by
  simp [polynomialAtInfinity]

/-- The point `(0 : 5 : 0)` of the projective curve is `(0 : 1 : 0)`. -/
example : (![0, 5, 0] : Fin 3 → ℚ) ≈ ![0, 1, 0] :=
  Projective.equiv_zero_of_equation_of_Z_eq_zero (W := E.toProjective)
    (by rw [equation_iff]; simp) (fun h ↦ by simpa using congrFun h 1) rfl

/-- The affine point `(2, 2)` is the point `(z, w) = (1, 1 / 2)` of the chart at infinity. -/
example : MvPolynomial.aeval ![(1 : ℚ), 1 / 2] E.polynomialAtInfinity = 0 := by
  have h := (Projective.equation_iff_aeval_polynomialAtInfinity E
    (P := ![2, 2, 1]) (by norm_num)).mp (by rw [equation_iff]; norm_num)
  norm_num at h
  exact h

/-- The identity `w³ g(z / w, 1 / w) = h(z, w)` at `z = 1`, `w = 2` in `ℚ`. -/
example : (2 : ℚ) ^ 3 * (E.baseChange ℚ).toAffine.polynomial.evalEval (1 * (1 / 2)) (1 / 2) =
    MvPolynomial.aeval ![(1 : ℚ), 2] E.polynomialAtInfinity := by
  have h := E.pow_three_mul_evalEval_polynomial_div (S := ℚ) 1 (Units.mk0 2 two_ne_zero)
  simpa using h

/-- The isomorphism of the charts sends `y` to `1 / w`, and its inverse sends `w` back to
`1 / y`. -/
example : E.awayYEquivAwayW.symm (E.awayYEquivAwayW (algebraMap _ _ E.affineY)) =
    algebraMap _ _ E.affineY := by
  simp

example : E.awayYEquivAwayW (algebraMap _ _ E.affineY) =
    IsLocalization.Away.invSelf E.wAtInfinity :=
  E.awayYEquivAwayW_affineY

end WeierstrassCurve.ChartAtInfinityTest
