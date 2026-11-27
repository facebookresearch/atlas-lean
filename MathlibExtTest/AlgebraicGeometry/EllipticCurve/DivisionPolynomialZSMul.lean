/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.DivisionPolynomialZSMul

@[expose] public noncomputable section

open Polynomial WeierstrassCurve
open scoped Polynomial.Bivariate

namespace DivisionPolynomialZSMulTest

/-- Consumer of the Jacobian formula for `n • (x, y)`. -/
private theorem exactSource {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)
    {x y : F} (h : W.toAffine.Nonsingular x y) (n : ℤ) :
    (n • Jacobian.Point.fromAffine (Affine.Point.some x y h)).point = ⟦W.smulEval x y n⟧ :=
  W.zsmul_eq_smulEval h n

/-- Consumer of the coprimality of `Φₙ` and `ΨSqₙ`. -/
private theorem exactSourceCoprime {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
    [IsAlgClosed K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : 0 < n) :
    IsCoprime ((W.baseChange K).Φ n) ((W.baseChange K).ΨSq n) :=
  W.isCoprime_Φ_ΨSq hn

/-- Boundary case `n = 1` of the torsion criterion: since `ψ₁ = 1`, no affine point is killed by
`1`. -/
example {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) : (1 : ℤ) • Affine.Point.some x y h ≠ 0 := by
  rw [Ne, W.smul_eq_zero_iff_evalEval_ψ h, ψ_one, evalEval_one]
  exact one_ne_zero

/-- The case `n = 2` of the torsion criterion: points of order two are the zeros of `ψ₂`. -/
example {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F) {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    (2 : ℤ) • Affine.Point.some x y h = 0 ↔ W.ψ₂.evalEval x y = 0 := by
  rw [W.smul_eq_zero_iff_evalEval_ψ h, ψ_two]

/-- The case `n = 2` of `evalEval_ψ_sq_of_commRing`, over a commutative ring:
`ψ₂(x, y) ^ 2 = Ψ₂Sq(x)`. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) : W.ψ₂.evalEval x y ^ 2 = W.Ψ₂Sq.eval x := by
  simpa using W.evalEval_ψ_sq_of_commRing h 2

/-- The case `n = 1` of `evalEval_φ_of_commRing`: `φ₁(x, y) = x`. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x y : R}
    (h : W.toAffine.Equation x y) : (W.φ 1).evalEval x y = x := by
  simpa using W.evalEval_φ_of_commRing h 1

end DivisionPolynomialZSMulTest

end
