/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicGeometry.EllipticCurve.ProjectiveWeierstrassPrime

namespace MathlibExtTest.AlgebraicGeometry.EllipticCurve.ProjectiveWeierstrassPrime

open MvPolynomial WeierstrassCurve.Projective

/-- Unfolding consumer: the cubic attached to a projective curve over `ℚ`
has the stated constant coefficient. -/
example (V : WeierstrassCurve.Projective ℚ) :
    (weierstrassCubic V).toPoly.coeff 0
      = C V.a₆ * X 1 ^ 3 - X 0 ^ 2 * X 1 - C V.a₃ * X 0 * X 1 ^ 2 :=
  weierstrassCubic_toPoly_coeff_zero V

/-- Characterization consumer with the original binders: separating the
first variable gives the negative cubic polynomial. -/
example {F : Type*} [CommRing F] (V : WeierstrassCurve.Projective F) :
    finSuccEquiv F 2 V.polynomial = -(weierstrassCubic V).toPoly :=
  finSuccEquiv_polynomial V

/-- Nontrivial instance: for the curve `⟨0, 0, 1, 0, 0⟩` over `ℚ`, the
projective polynomial is prime. -/
example : Prime (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve ℚ).toProjective.polynomial :=
  prime_polynomial _

/-- Nontrivial instance: the quotient by that polynomial is a domain and
the polynomial is homogeneous of degree `3` with total degree `3`. -/
example :
    IsDomain (MvPolynomial (Fin 3) ℚ ⧸
      Ideal.span {(⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve ℚ).toProjective.polynomial}) :=
  isDomain_quotient_span_polynomial _

example :
    (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve ℚ).toProjective.polynomial.IsHomogeneous 3 :=
  isHomogeneous_polynomial _

example :
    (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve ℚ).toProjective.polynomial.totalDegree = 3 :=
  totalDegree_polynomial _

/-- Boundary example: the polynomial depends on the curve. Over `ℚ` the two
explicit curves below take the values `2` and `1` at `![0, 1, 1]`, so their
polynomials differ. -/
example :
    (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve ℚ).toProjective.polynomial ≠
      (⟨0, 0, 0, 1, 0⟩ : WeierstrassCurve ℚ).toProjective.polynomial := by
  intro h
  have hA : MvPolynomial.eval ![(0 : ℚ), 1, 1]
      (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve ℚ).toProjective.polynomial = 2 := by
    rw [WeierstrassCurve.Projective.eval_polynomial]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  have hB : MvPolynomial.eval ![(0 : ℚ), 1, 1]
      (⟨0, 0, 0, 1, 0⟩ : WeierstrassCurve ℚ).toProjective.polynomial = 1 := by
    rw [WeierstrassCurve.Projective.eval_polynomial]
    norm_num [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
  rw [h, hB] at hA
  norm_num at hA

end MathlibExtTest.AlgebraicGeometry.EllipticCurve.ProjectiveWeierstrassPrime
