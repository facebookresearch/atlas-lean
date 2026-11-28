/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.EllipticCurve.AffineInvariantDifferential

/-!
# The two affine coordinate rings of a Weierstrass curve

For a Weierstrass curve `W` over a field `F`, `WeierstrassCurve.MvCoordinateRing` is
`F[x, y] / (f_W)` with `F[x, y] = MvPolynomial (Fin 2) F`, and Mathlib's
`WeierstrassCurve.Affine.CoordinateRing` is `F[X][Y] / (f_W)`. Mathlib's `F`-algebra isomorphism
`Polynomial.Bivariate.equivMvPolynomial F : F[X][Y] ≃ F[x, y]`, `X ↦ x`, `Y ↦ y`, carries one
Weierstrass polynomial to the other (`WeierstrassCurve.equivMvPolynomial_polynomial`) and so
induces an `F`-algebra isomorphism of the coordinate rings
(`WeierstrassCurve.mvCoordinateRingEquiv`), with `x̄ ↦ X̄` and `ȳ ↦ Ȳ`.
-/

@[expose] public section

open MvPolynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {F : Type*} [Field F]

theorem span_polynomial_eq_map (W : WeierstrassCurve F) :
    Ideal.span {W.toAffine.polynomial} =
      (Ideal.span {W.affineMvPolynomial}).map (Polynomial.Bivariate.equivMvPolynomial F).symm := by
  rw [Ideal.map_span, Set.image_singleton, ← W.equivMvPolynomial_polynomial,
    AlgEquiv.symm_apply_apply]

/-- **The two affine coordinate rings of a Weierstrass curve are isomorphic**: the `F`-algebra
isomorphism `F[x, y] / (f_W) ≅ F[X][Y] / (f_W)` (`WeierstrassCurve.MvCoordinateRing` and
Mathlib's `WeierstrassCurve.Affine.CoordinateRing`) induced by `x ↦ X`, `y ↦ Y`, that is, by the
inverse of `Polynomial.Bivariate.equivMvPolynomial F`. -/
noncomputable def mvCoordinateRingEquiv (W : WeierstrassCurve F) :
    W.MvCoordinateRing ≃ₐ[F] W.toAffine.CoordinateRing :=
  Ideal.quotientEquivAlg _ _ (Polynomial.Bivariate.equivMvPolynomial F).symm
    W.span_polynomial_eq_map

theorem mvCoordinateRingEquiv_mvMk (W : WeierstrassCurve F) (p : MvPolynomial (Fin 2) F) :
    W.mvCoordinateRingEquiv (W.mvMk p) =
      AdjoinRoot.mk W.toAffine.polynomial ((Polynomial.Bivariate.equivMvPolynomial F).symm p) :=
  Ideal.quotientEquivAlg_mk _ _ _ p

/-- The isomorphism sends `x̄` to `X̄` and `ȳ` to `Ȳ`. -/
theorem mvCoordinateRingEquiv_X (W : WeierstrassCurve F) :
    W.mvCoordinateRingEquiv (W.mvMk (X 0)) =
        AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X) ∧
      W.mvCoordinateRingEquiv (W.mvMk (X 1)) =
        AdjoinRoot.mk W.toAffine.polynomial Polynomial.X := by
  rw [mvCoordinateRingEquiv_mvMk, mvCoordinateRingEquiv_mvMk,
    Polynomial.Bivariate.equivMvPolynomial_symm_X_0,
    Polynomial.Bivariate.equivMvPolynomial_symm_X_1]
  exact ⟨rfl, rfl⟩

/-- The inverse isomorphism is induced by `WeierstrassCurve.toMvCoordinateRing`:
it sends the class of `p ∈ F[X][Y]` to `p(x̄, ȳ)`. -/
theorem mvCoordinateRingEquiv_symm_mk (W : WeierstrassCurve F) (p : F[X][Y]) :
    W.mvCoordinateRingEquiv.symm (AdjoinRoot.mk W.toAffine.polynomial p) =
      W.toMvCoordinateRing p := by
  apply W.mvCoordinateRingEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  change _ = W.mvCoordinateRingEquiv (W.mvMk (Polynomial.Bivariate.equivMvPolynomial F p))
  rw [mvCoordinateRingEquiv_mvMk, AlgEquiv.symm_apply_apply]

end WeierstrassCurve
