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
`WeierstrassCurve.Affine.CoordinateRing` is `F[X][Y] / (f_W)`. The `F`-algebra isomorphism
`F[x, y] ≅ F[X][Y]`, `x ↦ X`, `y ↦ Y`, carries one Weierstrass polynomial to the other and so
induces an `F`-algebra isomorphism of the coordinate rings
(`WeierstrassCurve.mvCoordinateRingEquiv`), with `x̄ ↦ X̄` and `ȳ ↦ Ȳ`.
-/

@[expose] public section

open MvPolynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {F : Type*} [Field F]

/-- `bivariateToMvPolynomial` as an `F`-algebra homomorphism `F[X][Y] → F[x, y]`. -/
noncomputable def bivariateToMvPolynomialAlgHom : F[X][Y] →ₐ[F] MvPolynomial (Fin 2) F :=
  { bivariateToMvPolynomial with
    commutes' := fun r ↦ by
      change bivariateToMvPolynomial (Polynomial.C (Polynomial.C r)) = _
      rw [bivariateToMvPolynomial_CC, MvPolynomial.algebraMap_eq] }

/-- **`F[x, y] ≅ F[X][Y]`**: the `F`-algebra isomorphism with `x ↦ X` (`Polynomial.C X`) and
`y ↦ Y`, whose inverse is `bivariateToMvPolynomial`. -/
noncomputable def mvPolynomialEquivBivariate : MvPolynomial (Fin 2) F ≃ₐ[F] F[X][Y] :=
  AlgEquiv.ofAlgHom (aeval ![Polynomial.C Polynomial.X, Polynomial.X]) bivariateToMvPolynomialAlgHom
    (by
      apply AlgHom.toRingHom_injective
      refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext (fun a ↦ ?_) ?_) ?_ <;>
        simp [bivariateToMvPolynomialAlgHom, bivariateToMvPolynomial])
    (by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i <;> simp [bivariateToMvPolynomialAlgHom, bivariateToMvPolynomial])

theorem mvPolynomialEquivBivariate_mvPolynomial (W : WeierstrassCurve F) :
    mvPolynomialEquivBivariate W.mvPolynomial = W.toAffine.polynomial := by
  simp [mvPolynomialEquivBivariate, mvPolynomial, Affine.polynomial]
  ring

theorem span_polynomial_eq_map (W : WeierstrassCurve F) :
    Ideal.span {W.toAffine.polynomial} =
      (Ideal.span {W.mvPolynomial}).map (mvPolynomialEquivBivariate (F := F)) := by
  rw [Ideal.map_span, Set.image_singleton]
  change _ = Ideal.span {mvPolynomialEquivBivariate W.mvPolynomial}
  rw [mvPolynomialEquivBivariate_mvPolynomial]

/-- **The two affine coordinate rings of a Weierstrass curve are isomorphic**: the `F`-algebra
isomorphism `F[x, y] / (f_W) ≅ F[X][Y] / (f_W)` (`WeierstrassCurve.MvCoordinateRing` and
Mathlib's `WeierstrassCurve.Affine.CoordinateRing`) induced by `x ↦ X`, `y ↦ Y`. -/
noncomputable def mvCoordinateRingEquiv (W : WeierstrassCurve F) :
    W.MvCoordinateRing ≃ₐ[F] W.toAffine.CoordinateRing :=
  Ideal.quotientEquivAlg _ _ mvPolynomialEquivBivariate W.span_polynomial_eq_map

theorem mvCoordinateRingEquiv_mvMk (W : WeierstrassCurve F) (p : MvPolynomial (Fin 2) F) :
    W.mvCoordinateRingEquiv (W.mvMk p) =
      AdjoinRoot.mk W.toAffine.polynomial (mvPolynomialEquivBivariate p) :=
  Ideal.quotientEquivAlg_mk _ _ _ p

/-- The isomorphism sends `x̄` to `X̄` and `ȳ` to `Ȳ`. -/
theorem mvCoordinateRingEquiv_X (W : WeierstrassCurve F) :
    W.mvCoordinateRingEquiv (W.mvMk (X 0)) =
        AdjoinRoot.mk W.toAffine.polynomial (Polynomial.C Polynomial.X) ∧
      W.mvCoordinateRingEquiv (W.mvMk (X 1)) =
        AdjoinRoot.mk W.toAffine.polynomial Polynomial.X := by
  rw [mvCoordinateRingEquiv_mvMk, mvCoordinateRingEquiv_mvMk]
  simp [mvPolynomialEquivBivariate]

/-- The inverse isomorphism is induced by `WeierstrassCurve.toMvCoordinateRing`:
it sends the class of `p ∈ F[X][Y]` to `p(x̄, ȳ)`. -/
theorem mvCoordinateRingEquiv_symm_mk (W : WeierstrassCurve F) (p : F[X][Y]) :
    W.mvCoordinateRingEquiv.symm (AdjoinRoot.mk W.toAffine.polynomial p) =
      W.toMvCoordinateRing p := by
  apply W.mvCoordinateRingEquiv.injective
  rw [AlgEquiv.apply_symm_apply]
  have hp : p = mvPolynomialEquivBivariate (bivariateToMvPolynomial p) :=
    (mvPolynomialEquivBivariate.apply_symm_apply p).symm
  have hring : W.toMvCoordinateRing = W.mvMk.toRingHom.comp bivariateToMvPolynomial := by
    refine Polynomial.ringHom_ext' (Polynomial.ringHom_ext (fun a ↦ ?_) ?_) ?_ <;>
      simp [toMvCoordinateRing, bivariateToMvPolynomial]
  have : W.toMvCoordinateRing p = W.mvMk (bivariateToMvPolynomial p) := by
    rw [hring]
    rfl
  rw [this, mvCoordinateRingEquiv_mvMk, ← hp]

end WeierstrassCurve
